#!/usr/bin/env python3
"""Regenerate upstream print observations after building in the upstream Nix shell."""

import argparse
import json
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[3]

import sys
sys.path.insert(0, str(ROOT / "scripts"))
from oracle_build import compile_probe
UPSTREAM = ROOT / "upstream/p4-spectec"
BUILD = UPSTREAM / "_build/default/p4spec/lib"
SCRATCH = ROOT / ".artifacts/print-oracle"
FIXTURE = ROOT / "P4SpecTecTest/Oracle/Print/observed.json"
LIBRARIES = [
    ("util", "util"), ("cache", "cache"), ("domain", "domain"),
    ("diagnostic", "diagnostic"), ("lang", "lang"), ("frontend", "frontend"),
    ("runtime/error_runtime", "error_runtime"), ("runtime/type", "type"),
    ("runtime/value", "value"), ("runtime", "runtime"), ("interface/p4", "p4"),
]


def observations():
    """Run the real printer against synthetic inputs and record its pinned revision."""
    entry = subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-files", "--stage", "--", "upstream/p4-spectec"],
        text=True,
    ).split()
    revision = subprocess.check_output(
        ["git", "-C", str(UPSTREAM), "rev-parse", "HEAD"], text=True,
    ).strip()
    if len(entry) != 4 or entry[0] != "160000" or entry[1] != revision:
        raise SystemExit("upstream HEAD does not match the indexed submodule pin")
    executable = compile_probe(
        UPSTREAM, probe=ROOT / "P4SpecTecTest/Oracle/Print/probe.ml", scratch=SCRATCH,
        libraries=LIBRARIES, rebuild=False,
        packages="core_unix.sys_unix,bignum.bigint,yojson,ppx_deriving_yojson.runtime,"
                 "uucp,uuseg,uutf,str,menhirLib")
    cases = json.loads(subprocess.check_output([str(executable)], cwd=ROOT))
    return {"upstreamRevision": revision, "cases": cases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare without updating fixtures")
    args = parser.parse_args()
    result = observations()
    text = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.check:
        if FIXTURE.read_text(encoding="utf-8") != text:
            raise SystemExit("print oracle fixtures are stale; rerun P4SpecTecTest/Oracle/Print/capture.py")
    else:
        FIXTURE.write_text(text, encoding="utf-8")
    print(f"[print-oracle] {len(result['cases'])} cases from {result['upstreamRevision']}")


if __name__ == "__main__":
    main()
