#!/usr/bin/env python3
"""Regenerate state observations from the actual pinned upstream AL interpreter."""

import argparse
import json
import pathlib
import shutil
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "test/state/observed.json"
SCRATCH = ROOT / ".artifacts/state-oracle"
LIBRARIES = [
    ("util", "util"), ("cache", "cache"), ("domain", "domain"),
    ("diagnostic", "diagnostic"), ("lang", "lang"), ("frontend", "frontend"),
    ("runtime/error_runtime", "error_runtime"), ("runtime/type", "type"),
    ("runtime/value", "value"), ("runtime/dynamic-runner", "dynamic_runner"),
    ("runtime/dynamic", "dynamic"), ("runtime/dynamic-al", "dynamic_al"),
    ("runtime/static", "static"), ("runtime/prose", "prose"),
    ("runtime", "runtime"), ("interface/builtin", "builtin"),
    ("pass", "pass"),
    ("interface/nano", "nano"), ("interface/p4", "p4"),
    ("interface/spectec", "spectec"), ("interface", "interface"),
    ("interp/inst", "inst"), ("interp/interp-common", "interp_common"),
    ("interp/interp-al", "interp_al"),
]


def observations(upstream):
    """Compile and run the real interpreter at the indexed submodule revision."""
    entry = subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-files", "--stage", "--", "upstream/p4-spectec"],
        text=True,
    ).split()
    revision = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True,
    ).strip()
    prefix = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "--show-prefix"], text=True,
    ).strip()
    if prefix or len(entry) != 4 or entry[0] != "160000" or entry[1] != revision:
        raise SystemExit("upstream HEAD does not match the indexed submodule pin")
    build = upstream / "_build/default/p4spec/lib"
    SCRATCH.mkdir(parents=True, exist_ok=True)
    source = SCRATCH / "probe.ml"
    shutil.copyfile(ROOT / "test/state/probe.ml", source)
    command = ["ocamlfind", "ocamlopt", "-linkpkg", "-package",
               "core_unix,core_unix.sys_unix,bignum.bigint,yojson,ppx_deriving_yojson.runtime,"
               "uucp,uuseg,uutf,str,menhirLib"]
    for directory, name in LIBRARIES:
        command += ["-I", str(build / directory / f".{name}.objs/byte"),
                    "-I", str(build / directory / f".{name}.objs/native")]
    command += [str(build / directory / f"{name}.cmxa") for directory, name in LIBRARIES]
    command += [str(source), "-o", str(SCRATCH / "probe")]
    subprocess.run(command, check=True, cwd=ROOT)
    cases = json.loads(subprocess.check_output([str(SCRATCH / "probe")], cwd=ROOT))
    return {"upstreamRevision": revision, "cases": cases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=pathlib.Path,
                        default=ROOT / "upstream/p4-spectec",
                        help="built upstream checkout at the indexed revision")
    parser.add_argument("--check", action="store_true", help="compare without updates")
    args = parser.parse_args()
    if not args.upstream.is_absolute():
        parser.error("--upstream must be an absolute path")
    result = observations(args.upstream.resolve())
    output = json.dumps(result, ensure_ascii=True, indent=2) + "\n"
    if args.check:
        if FIXTURE.read_text(encoding="utf-8") != output:
            raise SystemExit("state oracle fixtures are stale; rerun test/state/run.py")
    else:
        FIXTURE.write_text(output, encoding="utf-8")
    print(f"[state-oracle] {len(result['cases'])} cases from {result['upstreamRevision']}")


if __name__ == "__main__":
    main()
