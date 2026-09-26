#!/usr/bin/env python3
"""Read-only exact-pin oracle for bounded packet operations and dynamic Nano extract."""

import argparse
import importlib.util
import json
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]


def observations(upstream):
    spec = importlib.util.spec_from_file_location("p4_oracle", ROOT / "scripts/export-p4-oracle.py")
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    revision = oracle.revision_guard(upstream)
    oracle.PROBE = ROOT / "test/nano-target/probe.ml"
    oracle.SCRATCH = ROOT / ".artifacts/nano-target-oracle"
    executable = oracle.compile_probe(upstream)
    requests = json.loads((ROOT / "test/nano-target/requests.json").read_text())
    cases = []
    for request in requests:
        raw = subprocess.check_output(
            [str(executable), json.dumps(request)], cwd=ROOT, timeout=30, text=True)
        result = json.loads(raw)
        cases.append({"request": request, "result": result})
    return {"upstreamRevision": revision, "scope": "data-and-dynamic-handler", "cases": cases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", required=True, type=pathlib.Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not args.upstream.is_absolute():
        parser.error("--upstream must be absolute")
    result = observations(args.upstream.resolve())
    if args.check:
        expected = json.loads((ROOT / "test/nano-target/observed.json").read_text())
        if result != expected:
            raise SystemExit("Nano target observations differ")
        print(f"[nano-target] {len(result['cases'])} exact-pin observations match")
    else:
        print(json.dumps(result, indent=2, ensure_ascii=True))


if __name__ == "__main__":
    main()
