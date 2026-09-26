#!/usr/bin/env python3
"""Replay the four pinned full-P4 AL observations through the Lean interpreter."""

import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
ORACLE_CHECK = ROOT / "test/p4-oracle/check.py"
FIXTURE = ROOT / "test/p4-oracle/observed.json"


def load_check():
    spec = importlib.util.spec_from_file_location("p4_oracle_check", ORACLE_CHECK)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate_fixture(fixture, revision, expected_cases):
    if (not isinstance(fixture, dict)
            or set(fixture) != {"upstreamRevision", "cases"}
            or fixture["upstreamRevision"] != revision):
        raise ValueError("fixture revision differs from the pinned source")
    cases = fixture["cases"]
    if (not isinstance(cases, list) or len(cases) != len(expected_cases)
            or any(not isinstance(case, dict)
                   or set(case) != {"name", "source", "path", "expected"}
                   or not isinstance(case["expected"], dict)
                   or not case["expected"] for case in cases)
            or tuple((c["name"], c["source"], c["path"]) for c in cases)
            != expected_cases):
        raise ValueError("fixture case manifest or expectation is malformed")
    return cases


def collect(check, upstream, p4c):
    adapter = check.load_export()
    revision = adapter.revision_guard(upstream)
    check.p4c_pin_guard(upstream, p4c)
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    cases = validate_fixture(fixture, revision, check.EXPECTED_CASES)
    executable = adapter.compile_probe(upstream)
    roots = [(upstream, "$UPSTREAM"), (p4c, "$P4C"), (ROOT, "$REPO")]
    sources = {"upstream": upstream, "p4c": p4c, "repo": ROOT}
    replay = []
    for case in cases:
        program = sources[case["source"]] / case["path"]
        if not program.is_file():
            raise ValueError(f"missing pinned input: {program}")
        observed = adapter.observe(executable, upstream / "spec",
                                   p4c / "p4include", program)
        summary = check.summarize(observed, roots)
        check.check_cli(upstream, p4c / "p4include", program, summary)
        if summary != case["expected"]:
            raise ValueError(f"{case['name']}: upstream observation differs from fixture")
        replay.append({"name": case["name"], **observed})
    return {"schemaVersion": 1, "cases": replay}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--p4c", type=Path, required=True)
    args = parser.parse_args()
    if not args.upstream.is_absolute() or not args.p4c.is_absolute():
        parser.error("--upstream and --p4c must be absolute")
    upstream, p4c = args.upstream.resolve(), args.p4c.resolve()
    check = load_check()
    try:
        bundle = collect(check, upstream, p4c)
        with tempfile.TemporaryDirectory(prefix="p4-interp-replay-") as scratch:
            path = Path(scratch) / "bundle.json"
            path.write_text(json.dumps(bundle, ensure_ascii=True,
                                       separators=(",", ":")), encoding="utf-8")
            completed = subprocess.run(
                ["lake", "exe", "p4-interp-replay", str(path), "--sensitivity"], cwd=ROOT,
                check=False,
            )
            if completed.returncode:
                raise SystemExit(completed.returncode)
    except (ValueError, json.JSONDecodeError) as error:
        raise SystemExit(f"[p4-interp] {error}") from error


if __name__ == "__main__":
    main()
