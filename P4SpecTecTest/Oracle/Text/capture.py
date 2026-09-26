#!/usr/bin/env python3
"""Regenerate byte-level observations from pinned upstream text builtins."""

import argparse
import json
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[3]

import sys
sys.path.insert(0, str(ROOT / "scripts"))
from oracle_build import compile_probe
FIXTURE = ROOT / "P4SpecTecTest/Oracle/Text/observed.json"
SCRATCH = ROOT / ".artifacts/text-oracle"
LIBRARIES = [
    ("util", "util"), ("cache", "cache"), ("domain", "domain"),
    ("diagnostic", "diagnostic"), ("lang", "lang"), ("frontend", "frontend"),
    ("runtime/error_runtime", "error_runtime"), ("runtime/type", "type"),
    ("runtime/value", "value"), ("runtime", "runtime"),
    ("interface/builtin", "builtin"),
]


def observations(upstream):
    """Compile and execute the actual upstream wrappers at the indexed pin."""
    entry = subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-files", "--stage", "--", "upstream/p4-spectec"],
        text=True,
    ).split()
    revision = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True,
    ).strip()
    if len(entry) != 4 or entry[0] != "160000" or entry[1] != revision:
        raise SystemExit("upstream HEAD does not match the indexed submodule pin")
    build = upstream / "_build/default/p4spec/lib"
    executable = compile_probe(
        upstream, probe=ROOT / "P4SpecTecTest/Oracle/Text/probe.ml", scratch=SCRATCH,
        libraries=LIBRARIES, rebuild=False,
        packages="core_unix.sys_unix,bignum.bigint,yojson,ppx_deriving_yojson.runtime,"
                 "uucp,uuseg,uutf,str,menhirLib")
    cases = json.loads(subprocess.check_output([str(executable)], cwd=ROOT))
    return {"upstreamRevision": revision, "cases": cases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=pathlib.Path,
                        default=ROOT / "upstream/p4-spectec",
                        help="built upstream checkout at the indexed revision")
    parser.add_argument("--check", action="store_true", help="compare without updating fixtures")
    args = parser.parse_args()
    if not args.upstream.is_absolute():
        parser.error("--upstream must be an absolute path")
    result = observations(args.upstream.resolve())
    output = json.dumps(result, ensure_ascii=True, indent=2) + "\n"
    if args.check:
        if FIXTURE.read_text(encoding="utf-8") != output:
            raise SystemExit("text oracle fixtures are stale; rerun P4SpecTecTest/Oracle/Text/capture.py")
    else:
        FIXTURE.write_text(output, encoding="utf-8")
    print(f"[text-oracle] {len(result['cases'])} cases from {result['upstreamRevision']}")


if __name__ == "__main__":
    main()
