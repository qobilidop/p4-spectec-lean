#!/usr/bin/env python3
"""Regenerate upstream print observations after building in the upstream Nix shell."""

import argparse
import json
import pathlib
import shutil
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
UPSTREAM = ROOT / "upstream/p4-spectec"
BUILD = UPSTREAM / "_build/default/p4spec/lib"
SCRATCH = ROOT / ".artifacts/print-oracle"
FIXTURE = ROOT / "test/print/observed.json"
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
    SCRATCH.mkdir(parents=True, exist_ok=True)
    source = SCRATCH / "probe.ml"
    shutil.copyfile(ROOT / "test/print/probe.ml", source)
    command = ["ocamlfind", "ocamlopt", "-linkpkg", "-package",
               "core_unix.sys_unix,bignum.bigint,yojson,ppx_deriving_yojson.runtime,"
               "uucp,uuseg,uutf,str,menhirLib"]
    for directory, name in LIBRARIES:
        command += ["-I", str(BUILD / directory / f".{name}.objs/byte"),
                    "-I", str(BUILD / directory / f".{name}.objs/native")]
    command += [str(BUILD / directory / f"{name}.cmxa") for directory, name in LIBRARIES]
    command += [str(source), "-o", str(SCRATCH / "probe")]
    subprocess.run(command, check=True, cwd=ROOT)
    cases = json.loads(subprocess.check_output([str(SCRATCH / "probe")], cwd=ROOT))
    return {"upstreamRevision": revision, "cases": cases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare without updating fixtures")
    args = parser.parse_args()
    result = observations()
    text = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.check:
        if FIXTURE.read_text(encoding="utf-8") != text:
            raise SystemExit("print oracle fixtures are stale; rerun test/print/run.py")
    else:
        FIXTURE.write_text(text, encoding="utf-8")
    print(f"[print-oracle] {len(result['cases'])} cases from {result['upstreamRevision']}")


if __name__ == "__main__":
    main()
