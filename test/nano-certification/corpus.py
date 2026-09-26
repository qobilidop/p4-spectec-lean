#!/usr/bin/env python3
"""Inventory pinned Nano source cases; observation presence is not certification."""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "test/nano-certification/corpus.json"
UPSTREAM = "upstream/p4-spectec"
SPEC = "upstream/nano-p4-spec"
SOURCE = "nano-p4/testdata/"


class CorpusError(ValueError):
    """A missing, changed or falsely described corpus input."""


def git(checkout, *args):
    """Read exact Git objects without changing a checkout."""
    try:
        return subprocess.check_output(["git", "-C", str(checkout), *args],
                                       stderr=subprocess.PIPE)
    except subprocess.CalledProcessError as error:
        raise CorpusError(f"cannot read pinned Git input in {checkout}") from error


def digest(data):
    """Return a SHA-256 identity for source or evidence bytes."""
    return hashlib.sha256(data).hexdigest()


def indexed_pin(root, relative):
    """Read a unique stage-0 indexed gitlink, including a staged pin change."""
    entries = git(root, "ls-files", "--stage", "-z", "--", relative).split(b"\0")
    entries = [entry for entry in entries if entry]
    if len(entries) != 1:
        raise CorpusError(f"missing or unmerged indexed gitlink: {relative}")
    fields = entries[0].split(b"\t")
    if len(fields) != 2 or fields[1] != relative.encode():
        raise CorpusError(f"invalid indexed gitlink: {relative}")
    header = fields[0].split()
    if len(header) != 3 or header[0] != b"160000" or header[2] != b"0":
        raise CorpusError(f"invalid or unmerged indexed gitlink: {relative}")
    revision = header[1]
    if len(revision) != 40 or any(c not in b"0123456789abcdef" for c in revision):
        raise CorpusError(f"invalid indexed gitlink revision: {relative}")
    return revision.decode("ascii")


def pinned_file(checkout, revision, relative):
    """Require the on-disk input to equal its pinned Git object."""
    expected = git(checkout, "show", f"{revision}:{relative}")
    path = checkout / relative
    if not path.is_file() or path.is_symlink():
        raise CorpusError(f"missing corpus input: {path}")
    if path.read_bytes() != expected:
        raise CorpusError(f"modified pinned source: {path}")
    return {"path": relative, "sha256": digest(expected)}


def pinned_paths(checkout, revision, prefix):
    """Enumerate from Git, so deleting an on-disk case cannot hide it."""
    args = ["ls-tree", "-r", "--name-only", revision]
    if prefix:
        args.extend(["--", prefix])
    return git(checkout, *args).decode().splitlines()


def artifact(root, relative):
    """Describe existing upstream evidence without endorsing its meaning."""
    path = root / relative
    return {"path": relative, "sha256": digest(path.read_bytes())} if path.is_file() else None


def packet_observations(root, upstream_pin, spec_pin, sources):
    """Cross-link the already checked bounded upstream packet fixture."""
    path = root / "test/nano-target/fixture.py"
    spec = importlib.util.spec_from_file_location("nano_corpus_packet_fixture", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    try:
        bundle, data = module.read()
    except (ValueError, OSError) as error:
        raise CorpusError(f"invalid packet observation fixture: {error}") from error
    if (bundle["upstreamRevision"] != upstream_pin or bundle["nanoSpecRevision"] != spec_pin):
        raise CorpusError("packet observation fixture has stale pins")
    links = {}
    for index, case in enumerate(bundle["cases"]):
        if (case["program"] not in sources or case["stf"] not in sources
                or sources[case["program"]] != case["programSha256"]
                or sources[case["stf"]] != case["stfSha256"]):
            raise CorpusError("packet observation has stale source identity")
        # Dynamic-guard sessions are retained as boundary evidence, but do not
        # fulfill the sequential cache-free, guard-disabled profile.
        if case["guard"] is False:
            links.setdefault(case["stf"], []).append({
                "path": "test/nano-target/packet-observed.json.gz",
                "rawSha256": digest(data), "caseIndex": index,
                "outcome": case["observation"]["stfResult"],
                "category": "upstream-packet-observation"})
    return links


def generate(root=ROOT):
    """Recompute all source cases and evidence links from the current pins."""
    root = Path(root).resolve()
    pins = {name: indexed_pin(root, name) for name in (UPSTREAM, SPEC)}
    for name, revision in pins.items():
        if git(root / name, "rev-parse", "HEAD").decode().strip() != revision:
            raise CorpusError(f"checkout differs from recorded pin: {name}")
    upstream = root / UPSTREAM
    paths = pinned_paths(upstream, pins[UPSTREAM], SOURCE)
    paths = [p for p in paths if Path(p).suffix in (".p4", ".stf")]
    actual = {str(p.relative_to(upstream)) for p in (upstream / SOURCE).rglob("*")
              if p.suffix in (".p4", ".stf") and p.is_file()}
    if actual - set(paths):
        raise CorpusError("unrecorded corpus input: " + ", ".join(sorted(actual - set(paths))))
    inputs = [pinned_file(upstream, pins[UPSTREAM], p) for p in paths]
    sources = {item["path"]: item["sha256"] for item in inputs}
    includes = [pinned_file(upstream, pins[UPSTREAM], p)
                for p in pinned_paths(upstream, pins[UPSTREAM], "nano-p4/include")]
    specification = [pinned_file(root / SPEC, pins[SPEC], p)
                     for p in pinned_paths(root / SPEC, pins[SPEC], "")
                     if p.endswith(".watsup")]
    packets = packet_observations(root, pins[UPSTREAM], pins[SPEC], sources)
    cases = []
    for item in inputs:
        relative = item["path"]
        name = relative.removeprefix(SOURCE).rsplit(".", 1)[0]
        if relative.endswith(".p4"):
            prefix = f"exports/programs/nano-p4/{name}"
            evidence = []
            missing = []
            for suffix in (".json", ".verdict", ".verdict.sl", ".unparseable"):
                entry = artifact(root, prefix + suffix)
                if entry is not None:
                    evidence.append(entry)
            verdict_path = root / (prefix + ".verdict")
            verdict = verdict_path.read_text().strip() if verdict_path.is_file() else "unknown"
            if verdict not in ("pass", "fail", "unknown"):
                raise CorpusError(f"invalid typing verdict: {verdict_path}")
            required = [".json", ".verdict", ".verdict.sl"]
            if verdict != "unknown":
                required.append(".outputs.json" if verdict == "pass" else ".diagnostic")
            for suffix in required:
                entry = artifact(root, prefix + suffix)
                if entry is None:
                    missing.append(prefix + suffix)
                elif entry not in evidence:
                    evidence.append(entry)
            cases.append({"id": f"corpus:typing:{name}", "kind": "typing",
                          "source": item, "upstreamVerdict": verdict,
                          "observationCategory": "upstream-typing-export",
                          "observations": evidence, "missingObservations": missing,
                          "requiredEvidence": "generated-and-reference-typing-replay"})
        else:
            program = relative.removesuffix(".stf") + ".p4"
            if program not in sources:
                raise CorpusError(f"STF has no pinned source program: {relative}")
            cases.append({"id": f"corpus:packet:{name}", "kind": "packet",
                          "source": item, "programId": f"corpus:typing:{name}",
                          "observations": packets.get(relative, []),
                          "requiredEvidence": "generated-reference-upstream-packet-replay"})
    return {"schemaVersion": 1, "pins": pins,
            "profile": {"cache": False, "dynamicGuards": False, "sequential": True},
            "includes": includes, "specification": specification, "cases": cases}


def strict_object(pairs):
    """Reject duplicate JSON keys rather than silently keeping the last value."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise CorpusError(f"duplicate manifest key: {key}")
        result[key] = value
    return result


def load(path=MANIFEST):
    """Load the manifest without losing duplicate-key errors."""
    try:
        return json.loads(Path(path).read_text(), object_pairs_hook=strict_object,
                          parse_constant=lambda value: (_ for _ in ()).throw(
                              CorpusError(f"invalid JSON constant: {value}")))
    except (OSError, json.JSONDecodeError) as error:
        raise CorpusError(f"cannot load corpus manifest: {path}") from error


def check_manifest(manifest, root=ROOT):
    """Reject omitted cases, extra flags, changed identities and stale evidence."""
    expected = generate(root)
    # Python equality equates True with 1 and False with 0. Compare canonical
    # JSON so profile flags, schema versions and observation indices keep types.
    canonical = lambda value: json.dumps(value, sort_keys=True, separators=(",", ":"))
    if canonical(manifest) != canonical(expected):
        if not isinstance(manifest, dict) or set(manifest) != set(expected):
            raise CorpusError("corpus manifest schema differs")
        if manifest["pins"] != expected["pins"]:
            raise CorpusError("corpus manifest pins differ")
        if canonical(manifest["cases"]) != canonical(expected["cases"]):
            raise CorpusError("corpus case inventory or evidence differs")
        raise CorpusError("corpus source context or profile differs")
    return obligation_ids(manifest)


def obligation_ids(manifest):
    """Stable IDs for all required replay cases, including typing failures."""
    return [case["id"] for case in manifest["cases"]]


def check(root=ROOT, path=MANIFEST):
    """Load and freshness-check the canonical manifest; return all obligations."""
    return check_manifest(load(path), root)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--update", action="store_true")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    if args.update and args.strict:
        parser.error("--update and --strict are mutually exclusive")
    try:
        if args.update:
            manifest = generate()
            MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n")
        else:
            manifest = load()
            check_manifest(manifest)
        typing = [case for case in manifest["cases"] if case["kind"] == "typing"]
        packets = [case for case in manifest["cases"] if case["kind"] == "packet"]
        print(f"[nano-corpus] {len(typing)} programs, {len(packets)} STF sessions; "
              "inventory fresh")
        print(f"[nano-corpus] upstream observations: {sum(bool(c['observations']) for c in typing)} "
              f"typing, {sum(bool(c['observations']) for c in packets)} packet")
        missing = sum(bool(c["missingObservations"]) for c in typing)
        unknown = sum(c["upstreamVerdict"] == "unknown" for c in typing)
        absent_packets = sum(not c["observations"] for c in packets)
        print(f"[nano-corpus] outstanding observations: {missing} incomplete typing bundles, "
              f"{unknown} unknown verdicts, {absent_packets} STF sessions")
        print(f"[nano-corpus] {len(manifest['cases'])} replay evidence obligations outstanding; "
              "observation presence is not certification")
        if args.strict:
            print("[nano-corpus] strict completion rejected: checked replay evidence absent")
            return 1
        return 0
    except CorpusError as error:
        print(f"[nano-corpus] {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
