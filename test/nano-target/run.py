#!/usr/bin/env python3
"""Read-only exact-pin oracle for bounded packet operations and dynamic Nano extract."""

import argparse
import importlib.util
import json
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]


def observations(upstream, driver=False):
    spec = importlib.util.spec_from_file_location("p4_oracle", ROOT / "scripts/export-p4-oracle.py")
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    revision = oracle.revision_guard(upstream)
    oracle.PROBE = ROOT / ("test/nano-target/driver-probe.ml" if driver
                           else "test/nano-target/probe.ml")
    oracle.SCRATCH = ROOT / (".artifacts/nano-driver-oracle" if driver
                             else ".artifacts/nano-target-oracle")
    executable = oracle.compile_probe(upstream)
    prefix = "driver-" if driver else ""
    requests = json.loads((ROOT / f"test/nano-target/{prefix}requests.json").read_text())
    cases = []
    for request in requests:
        raw = subprocess.check_output(
            [str(executable), json.dumps(request)], cwd=ROOT, timeout=30, text=True)
        result = json.loads(raw)
        cases.append({"request": request, "result": result})
    return {"upstreamRevision": revision,
            "scope": "dynamic-driver" if driver else "data-and-dynamic-handler", "cases": cases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", required=True, type=pathlib.Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--driver", action="store_true")
    parser.add_argument("--update", action="store_true")
    args = parser.parse_args()
    if not args.upstream.is_absolute():
        parser.error("--upstream must be absolute")
    if args.check and args.update:
        parser.error("--check and --update are mutually exclusive")
    if args.update and not args.driver:
        parser.error("--update is only supported for the new driver fixture")
    result = observations(args.upstream.resolve(), args.driver)
    prefix = "driver-" if args.driver else ""
    fixture = ROOT / f"test/nano-target/{prefix}observed.json"
    if args.check:
        expected = json.loads(fixture.read_text())
        if result != expected:
            raise SystemExit("Nano target observations differ")
        print(f"[nano-target] {len(result['cases'])} exact-pin observations match")
    elif args.update:
        fixture.write_text(json.dumps(result, indent=2, ensure_ascii=True) + "\n")
        print(f"[nano-driver] wrote {len(result['cases'])} exact-pin observations")
    else:
        print(json.dumps(result, indent=2, ensure_ascii=True))


if __name__ == "__main__":
    main()
