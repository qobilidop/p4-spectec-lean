#!/usr/bin/env python3
"""Capture real pinned Nano AL packet sessions without modifying target outputs."""

import argparse
import hashlib
import importlib.util
import json
import pathlib
import subprocess
import fixture

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
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--update", action="store_true")
    args = parser.parse_args()
    if args.check and args.update:
        parser.error("--check and --update are mutually exclusive")
    if not args.upstream.is_absolute() or not args.spec.is_absolute():
        parser.error("checkout paths must be absolute")
    oracle = load("nano_packet_oracle", ROOT / "scripts/export-p4-oracle.py")
    revision = oracle.revision_guard(args.upstream)
    spec_pin = subprocess.check_output(
        ["git", "-C", str(ROOT), "rev-parse", "HEAD:upstream/nano-p4-spec"], text=True).strip()
    actual_pin = subprocess.check_output(
        ["git", "-C", str(args.spec), "rev-parse", "HEAD"], text=True).strip()
    if actual_pin != spec_pin:
        raise SystemExit("Nano spec revision differs from gitlink")
    subprocess.run(["git", "-C", str(args.spec), "diff", "--exit-code", "HEAD"], check=True)
    oracle.PROBE = ROOT / "test/nano-target/packet-probe.ml"
    oracle.SCRATCH = ROOT / ".artifacts/nano-packet-oracle"
    executable = oracle.compile_probe(args.upstream)
    normalize = load("nano_packet_normalize", ROOT / "test/p4-oracle/check.py")
    cases = []
    for name, guard in [("free-pass", False), ("field-access", False),
                        ("action-call-table-2", False), ("field-access", True)]:
        prefix = args.upstream / "nano-p4/testdata/positive" / name
        program, stf = prefix.with_suffix(".p4"), prefix.with_suffix(".stf")
        raw = subprocess.check_output(
            [str(executable), str(args.spec), str(args.upstream / "nano-p4/include"),
             str(program), str(stf), str(guard).lower()], text=True, timeout=60)
        lines = [line.removeprefix("OBSERVATION ") for line in raw.splitlines()
                 if line.startswith("OBSERVATION ")]
        if len(lines) != 1:
            raise SystemExit("missing or repeated packet observation")
        result = normalize.normalize_locations(
            fixture.strict_json(lines[0]),
            [(args.upstream, "$UPSTREAM"), (args.spec, "$NANO_SPEC")])
        cases.append({"program": str(program.relative_to(args.upstream)),
                      "programSha256": hashlib.sha256(program.read_bytes()).hexdigest(),
                      "stf": str(stf.relative_to(args.upstream)),
                      "stfSha256": hashlib.sha256(stf.read_bytes()).hexdigest(),
                      "guard": guard, "observation": result})
    result = {"schemaVersion": 1, "relation": "NanoSwitch_drive",
              "upstreamRevision": revision, "nanoSpecRevision": spec_pin,
              "mode": "AL", "cache": False, "det": False, "cases": cases}
    fixture.validate(result)
    if args.check:
        expected, _ = fixture.read()
        if result != expected:
            raise SystemExit("packet observations differ")
        print(f"[nano-packet] {len(cases)} exact-pin sessions match")
    elif args.update:
        fixture.write(result)
        print(f"[nano-packet] wrote {len(cases)} exact-pin sessions")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
