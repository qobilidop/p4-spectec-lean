#!/usr/bin/env python3
"""Check bounded type-runtime observations from the indexed upstream pin."""

import argparse
import json
import pathlib
import shutil
import subprocess


ROOT = pathlib.Path(__file__).resolve().parents[3]
FIXTURE = ROOT / "P4SpecTecTest/Oracle/Type/observed.json"
SCRATCH = ROOT / ".artifacts/type-runtime-oracle"
import sys
sys.path.insert(0, str(ROOT / "scripts"))
from oracle_build import PATCHED_FILES, revision_guard
import oracle_build

LIBRARIES = [
    ("util", "util"), ("cache", "cache"), ("domain", "domain"),
    ("diagnostic", "diagnostic"), ("lang", "lang"), ("frontend", "frontend"),
    ("runtime/error_runtime", "error_runtime"), ("runtime/type", "type"),
    ("runtime/value", "value"), ("runtime", "runtime"),
]


def observations(upstream):
    """Rebuild and compile the probe against the verified pinned source."""
    revision = revision_guard(upstream)
    executable = oracle_build.compile_probe(
        upstream, probe=ROOT / "P4SpecTecTest/Oracle/Type/probe.ml", scratch=SCRATCH,
        libraries=LIBRARIES,
        packages="core_unix.sys_unix,bignum.bigint,yojson,ppx_deriving_yojson.runtime,"
                 "uucp,uuseg,uutf,str,menhirLib")
    cases = json.loads(subprocess.check_output([str(executable)], cwd=ROOT))
    return {"upstreamRevision": revision, "cases": cases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=pathlib.Path,
                        default=ROOT / "upstream/p4-spectec",
                        help="built upstream checkout at the indexed revision")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not args.upstream.is_absolute():
        parser.error("--upstream must be an absolute path")
    result = observations(args.upstream.resolve())
    output = json.dumps(result, ensure_ascii=True, indent=2) + "\n"
    if args.check:
        if FIXTURE.read_text(encoding="utf-8") != output:
            raise SystemExit("type-runtime oracle fixture is stale")
    else:
        FIXTURE.write_text(output, encoding="utf-8")
    print(f"[type-runtime] {len(result['cases'])} cases from {result['upstreamRevision']}")


if __name__ == "__main__":
    main()
