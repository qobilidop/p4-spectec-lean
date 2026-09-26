"""Capture independent request/response probes for NanoSwitch target and driver."""

import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
import oracle_build


def observations(upstream, suite, scope, scratch):
    """Run each suite request in a fresh pinned upstream probe process."""
    revision = oracle_build.revision_guard(upstream)
    executable = oracle_build.compile_probe(upstream, probe=suite / "probe.ml", scratch=scratch)
    requests = json.loads((suite / "requests.json").read_text())
    cases = []
    for request in requests:
        raw = subprocess.check_output(
            [str(executable), json.dumps(request)], cwd=ROOT, timeout=30, text=True)
        cases.append({"request": request, "result": json.loads(raw)})
    return {"upstreamRevision": revision, "scope": scope, "cases": cases}


def main(suite, scope, scratch, allow_update=False):
    """Compare or display a suite's observations; only the driver permits updates."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", required=True, type=Path)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    if allow_update:
        mode.add_argument("--update", action="store_true")
    args = parser.parse_args()
    if not args.upstream.is_absolute():
        parser.error("--upstream must be absolute")
    result = observations(args.upstream.resolve(), suite, scope, scratch)
    fixture = suite / "observed.json"
    if args.check:
        if result != json.loads(fixture.read_text()):
            raise SystemExit("Nano observations differ")
        print(f"[{suite.name.lower()}] {len(result['cases'])} exact-pin observations match")
    elif getattr(args, "update", False):
        fixture.write_text(json.dumps(result, indent=2, ensure_ascii=True) + "\n")
        print(f"[{suite.name.lower()}] wrote {len(result['cases'])} exact-pin observations")
    else:
        print(json.dumps(result, indent=2, ensure_ascii=True))
