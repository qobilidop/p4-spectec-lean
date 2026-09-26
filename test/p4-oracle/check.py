#!/usr/bin/env python3
"""Check bounded full-P4 observations against the pinned AL interpreter."""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "test/p4-oracle/observed.json"
EXPORT = ROOT / "scripts/export-p4-oracle.py"
EXPECTED_CASES = (
    ("basic-routing", "p4c", "testdata/p4_16_samples/basic_routing-bmv2.p4"),
    ("positive-regression", "upstream", "testdata/regression/pos/issue-212.p4"),
    ("negative-regression", "upstream", "testdata/regression/neg/issue-204.p4"),
    ("syntax-error", "repo", "test/p4-oracle/invalid.p4"),
)


def load_export():
    spec = importlib.util.spec_from_file_location("p4_oracle_export", EXPORT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def p4c_pin_guard(upstream, p4c):
    tree = subprocess.check_output(
        ["git", "-C", str(upstream), "ls-tree", "HEAD", "--", "p4c"], text=True,
    ).split()
    head = subprocess.check_output(
        ["git", "-C", str(p4c), "rev-parse", "HEAD"], text=True,
    ).strip()
    root = subprocess.check_output(
        ["git", "-C", str(p4c), "rev-parse", "--show-toplevel"], text=True,
    ).strip()
    dirty = subprocess.check_output(
        ["git", "-C", str(p4c), "status", "--porcelain"], text=True,
    )
    if (root != str(p4c) or len(tree) != 4 or tree[:3] !=
            ["160000", "commit", head] or dirty):
        raise SystemExit("p4c must be a clean checkout at upstream's pinned gitlink")


def source_path(path, roots):
    for root, label in roots:
        root = str(root)
        if path == root or path.startswith(root + "/"):
            return label + path[len(root):]
    return path


def source_region(value, roots):
    if (not isinstance(value, dict) or set(value) != {"left", "right"}
            or any(not isinstance(value[side], dict)
                   or set(value[side]) != {"file", "line", "column"}
                   or not isinstance(value[side]["file"], str)
                   for side in ("left", "right"))):
        return None
    return {side: {**value[side],
                   "file": source_path(value[side]["file"], roots)}
            for side in ("left", "right")}


def normalize_locations(value, roots):
    if isinstance(value, list):
        return [normalize_locations(item, roots) for item in value]
    if isinstance(value, dict):
        if set(value) == {"source", "code", "message", "region"}:
            return {**value, "region": path_in_diagnostic(value["region"], roots)}
        normalized = {}
        for key, item in value.items():
            if key == "at":
                region = source_region(item, roots)
                if region is not None:
                    normalized[key] = region
                    continue
            # ExternV's JSON is arbitrary semantic data, even when it has
            # fields shaped like a source region.
            if key == "it" and isinstance(item, list) and item[:1] == ["ExternV"]:
                normalized[key] = item
                continue
            normalized[key] = normalize_locations(item, roots)
        return normalized
    return value


def path_in_diagnostic(region, roots):
    # Only the rendered source-region field is normalized; diagnostic text
    # and semantic values retain literal checkout-path strings.
    for root, label in roots:
        region = region.replace(str(root), label)
    return region


def digest(value, roots):
    if value is None:
        return None
    encoded = json.dumps(normalize_locations(value, roots),
                         ensure_ascii=True, separators=(",", ":"))
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def summarize(observation, roots):
    summary = {"bootSha256": digest(observation["boot"], roots), "relations": {}}
    for name, run in observation["relations"].items():
        result = run["result"]
        entry = {
            "class": result["class"],
            "counterBefore": run["counterBefore"],
            "counterAfterBoot": run["counterAfterBoot"],
            "counterAfter": run["counterAfter"],
            "outputsSha256": digest(result.get("outputs"), roots),
            "outputArity": len(result["outputs"]) if "outputs" in result else None,
            "diagnosticSha256": digest(result.get("diagnostic"), roots),
        }
        summary["relations"][name] = entry
    return summary


def check_cli(upstream, includes, program, summary):
    executable = upstream / "_build/default/p4spec/bin/main.exe"
    if not executable.is_file():
        raise SystemExit(f"missing pinned upstream CLI: {executable}")
    for relation, result in summary["relations"].items():
        completed = subprocess.run(
            [str(executable), "run", str(upstream / "spec"), "-rel", relation,
             "-i", str(includes), "-p", str(program), "-al"],
            capture_output=True, text=True, cwd=ROOT,
        )
        success = result["class"] == "pass"
        valid = (completed.returncode == 0 and completed.stdout == "passed\n"
                 if success else completed.returncode == 1
                 and completed.stdout == "" and bool(completed.stderr))
        if not valid:
            raise SystemExit(f"CLI verdict differs for {program} {relation}: "
                             f"exit={completed.returncode}, stdout={completed.stdout!r}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--p4c", type=Path, required=True)
    parser.add_argument("--update", action="store_true")
    args = parser.parse_args()
    if not args.upstream.is_absolute() or not args.p4c.is_absolute():
        parser.error("--upstream and --p4c must be absolute")
    upstream = args.upstream.resolve()
    p4c = args.p4c.resolve()
    adapter = load_export()
    revision = adapter.revision_guard(upstream)
    p4c_pin_guard(upstream, p4c)
    executable = adapter.compile_probe(upstream)
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    if (not isinstance(fixture, dict)
            or set(fixture) != {"upstreamRevision", "cases"}
            or fixture["upstreamRevision"] != revision):
        raise SystemExit("fixture revision differs from indexed upstream")
    cases = fixture["cases"]
    if (not isinstance(cases, list) or
            tuple((case.get("name"), case.get("source"), case.get("path"))
                  for case in cases if isinstance(case, dict)) != EXPECTED_CASES
            or len(cases) != len(EXPECTED_CASES)
            or any(set(case) != {"name", "source", "path", "expected"}
                   or not isinstance(case["expected"], dict)
                   or not case["expected"] for case in cases)):
        raise SystemExit("oracle fixture case manifest or expectation is malformed")
    roots = [(upstream, "$UPSTREAM"), (p4c, "$P4C"), (ROOT, "$REPO")]
    sources = {"upstream": upstream, "p4c": p4c, "repo": ROOT}
    for case in cases:
        program = sources[case["source"]] / case["path"]
        if not program.is_file():
            raise SystemExit(f"missing pinned input: {program}")
        observation = adapter.observe(executable, upstream / "spec",
                                      p4c / "p4include", program)
        actual = summarize(observation, roots)
        check_cli(upstream, p4c / "p4include", program, actual)
        if args.update:
            case["expected"] = actual
        elif case.get("expected") != actual:
            raise SystemExit(f"stale observation for {case['name']}: {actual}")
        print(f"[p4-oracle] checked {case['name']}")
    if args.update:
        fixture["upstreamRevision"] = revision
        FIXTURE.write_text(json.dumps(fixture, indent=2, ensure_ascii=True) + "\n",
                           encoding="utf-8")


if __name__ == "__main__":
    main()
