#!/usr/bin/env python3
"""Verify the pinned session snapshot against the corpus inventory and replay it locally.

No network or OCaml is needed. Every packet obligation of the corpus inventory must have
exactly one session with matching source digests; the Lean replay then compares both Lean
paths with upstream and must report every session as matching. With `--summary FILE`, the
matched session identities are written as JSON for the completion checker.
"""

import argparse
import importlib.util
import json
import pathlib
import subprocess
import sys

import fixture

ROOT = fixture.ROOT


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_corpus(bundle):
    """Every inventory packet case appears once, with the pinned source digests."""
    corpus = load("nano_session_corpus", ROOT / "P4SpecTecTest/Oracle/Nano/Certification/corpus.py")
    manifest = corpus.load(corpus.MANIFEST)
    cases = {c["id"]: c for c in manifest["cases"]}
    packets = {i for i, c in cases.items() if c["kind"] == "packet"}
    sessions = {s["id"]: s for s in bundle["sessions"]}
    if set(sessions) != packets:
        raise SystemExit("session fixture does not cover exactly the corpus packet cases")
    for sid, session in sessions.items():
        case = cases[sid]
        program = cases[case["programId"]]
        if (session["stf"] != case["source"]["path"]
                or session["stfSha256"] != case["source"]["sha256"]
                or session["program"] != program["source"]["path"]
                or session["programSha256"] != program["source"]["sha256"]):
            raise SystemExit(f"session source identity differs from the inventory: {sid}")
        export = f"exports/programs/nano-p4/{program['id'].removeprefix('corpus:typing:')}.json"
        if session["export"] != export or not (ROOT / export).is_file():
            raise SystemExit(f"session program export differs or is missing: {sid}")
    return sorted(sessions)


def mutations(lean, bundle, scratch):
    """Each distinguishing mutation of an observation must be rejected for its session."""
    first = next(s for s in bundle["sessions"]
                 if any(d["class"] == "pass" and d["txs"] for d in s["drives"]))
    drive = next(d for d in first["drives"] if d["class"] == "pass" and d["txs"])
    # Replace a context by a decision and a decision by an architecture state: canonically
    # distinct values of a different shape, whatever the table order.

    def mutate(label, change):
        mutated = json.loads(json.dumps(bundle))
        session = next(s for s in mutated["sessions"] if s["id"] == first["id"])
        change(session, next(d for d in session["drives"] if d["rx"] == drive["rx"]))
        mutated["sessions"] = [session]
        path = scratch / "sessions-mutated.json"
        path.write_text(json.dumps(mutated))
        result = subprocess.run([str(lean), str(path)], cwd=ROOT, timeout=600,
                                capture_output=True, text=True)
        if result.returncode == 0 or "MISMATCH" not in result.stderr:
            raise SystemExit(f"session mutation accepted: {label}")

    mutate("transmission", lambda s, d: d.update(txs=[]))
    mutate("context", lambda s, d: d.update(ctx=d["decision"]))
    mutate("decision", lambda s, d: d.update(decision=d["arch"]))
    mutate("outcome", lambda s, d: d.update({"class": "runtimeFail"}) or
           [d.pop(k) for k in ("ctx", "arch", "decision", "txs")])
    mutate("initialization", lambda s, d: s["init"].update(ctx=d["decision"]))
    print("[nano-sessions] five observation mutations rejected")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=pathlib.Path,
                        default=ROOT / ".lake/build/bin/check-nano-sessions")
    parser.add_argument("--summary", type=pathlib.Path)
    args = parser.parse_args()
    bundle, data = fixture.read()
    ids = check_corpus(bundle)
    cache = ROOT / ".artifacts/nano-sessions/sessions-observed.json"
    cache.parent.mkdir(parents=True, exist_ok=True)
    snapshot = load("session_snapshot", ROOT / "scripts/spec-snapshot.py")
    snapshot.atomic_write(cache, data)
    result = subprocess.run([str(args.lean.resolve()), str(cache)], cwd=ROOT, timeout=1800,
                            capture_output=True, text=True)
    sys.stdout.write(result.stdout)
    sys.stderr.write(result.stderr)
    matched = sorted(line.split()[1] for line in result.stdout.splitlines()
                     if line.startswith("SESSION ") and line.endswith(" match"))
    if result.returncode != 0 or matched != ids:
        raise SystemExit("session replay did not match every corpus packet case")
    mutations(args.lean.resolve(), bundle, cache.parent)
    if args.summary:
        args.summary.write_text(json.dumps({"matched": matched}, indent=1) + "\n")
    print(f"[nano-sessions] {len(matched)} corpus sessions checked")


if __name__ == "__main__":
    main()
