#!/usr/bin/env python3
"""Capture exact-pin shared verify behavior and the Nano AL reachability boundary."""

import argparse
import importlib.util
import json
import pathlib
import subprocess
import contract

ROOT = pathlib.Path(__file__).resolve().parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=pathlib.Path, required=True)
    parser.add_argument("--spec", type=pathlib.Path, required=True)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--update", action="store_true")
    args = parser.parse_args()
    if not args.upstream.is_absolute() or not args.spec.is_absolute():
        parser.error("checkout paths must be absolute")
    oracle = load("verify_oracle", ROOT / "scripts/export-p4-oracle.py")
    revision = oracle.revision_guard(args.upstream)
    pin = subprocess.check_output(
        ["git", "-C", str(ROOT), "rev-parse", "HEAD:upstream/nano-p4-spec"], text=True).strip()
    spec_guard = load("verify_spec_guard", ROOT / "scripts/check-spec-pin.py")
    spec_guard.revision_guard(args.spec, pin)
    oracle.PROBE = ROOT / "test/nano-verify/probe.ml"
    oracle.SCRATCH = ROOT / ".artifacts/nano-verify-oracle"
    executable = oracle.compile_probe(args.upstream)

    def observe(arguments):
        output = subprocess.check_output([str(executable), *arguments],
                                         cwd=ROOT, text=True, timeout=60)
        lines = [line.removeprefix("OBSERVATION ") for line in output.splitlines()
                 if line.startswith("OBSERVATION ")]
        if len(lines) != 1:
            raise ValueError("missing or repeated observation")
        return contract.strict(lines[0])

    requests = contract.strict((ROOT / "test/nano-verify/requests.json").read_bytes())
    result = {"upstreamRevision": revision, "nanoSpecRevision": pin,
              "scope": "shared-verify-and-nano-dispatch", "cases": [
                  {"request": r, "result": observe([json.dumps(r)])} for r in requests],
              "nanoReachability": observe(["reachability", str(args.spec)])}
    contract.validate(result, requests)
    fixture = ROOT / "test/nano-verify/observed.json"
    if args.check:
        if result != contract.read()[0]:
            raise SystemExit("verify observations differ")
        print(f"[nano-verify] {len(requests)} direct observations and AL boundary match")
    elif args.update:
        fixture.write_text(json.dumps(result, indent=2) + "\n")
        print(f"[nano-verify] wrote {len(requests)} direct observations and AL boundary")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
