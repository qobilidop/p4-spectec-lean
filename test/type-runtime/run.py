#!/usr/bin/env python3
"""Check bounded type-runtime observations from the indexed upstream pin."""

import argparse
import json
import pathlib
import shutil
import subprocess


ROOT = pathlib.Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "test/type-runtime/observed.json"
SCRATCH = ROOT / ".artifacts/type-runtime-oracle"
PATCH = "upstream/patches/0001-json-export.patch"
PATCHED_FILES = (
    "p4spec/bin/main.ml", "p4spec/bin/nano.ml",
    "p4spec/lib/lang/al/ast.ml", "p4spec/lib/lang/il/ast.ml",
)
LIBRARIES = [
    ("util", "util"), ("cache", "cache"), ("domain", "domain"),
    ("diagnostic", "diagnostic"), ("lang", "lang"), ("frontend", "frontend"),
    ("runtime/error_runtime", "error_runtime"), ("runtime/type", "type"),
    ("runtime/value", "value"), ("runtime", "runtime"),
]


def revision_guard(upstream):
    """Require the indexed pin plus the exact committed export patch only."""
    entry = subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-files", "--stage", "--", "upstream/p4-spectec"],
        text=True,
    ).split()
    revision = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True,
    ).strip()
    source_root = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "--show-toplevel"], text=True,
    ).strip()
    if source_root != str(upstream) or len(entry) != 4 or entry[:2] != ["160000", revision]:
        raise SystemExit("upstream must be a repository root at the indexed pin")
    expected_patch = subprocess.check_output(["git", "-C", str(ROOT), "show", f"HEAD:{PATCH}"])
    actual_patch = subprocess.check_output(
        ["git", "-C", str(upstream), "diff", "HEAD", "--no-ext-diff", "--no-color", "--binary"]
    )
    status = subprocess.check_output(
        ["git", "-C", str(upstream), "status", "--short", "--untracked-files=all"],
        text=True,
    ).splitlines()
    if actual_patch != expected_patch or status != [f" M {path}" for path in PATCHED_FILES]:
        raise SystemExit("upstream source differs from the exact committed export patch")
    return revision


def observations(upstream):
    """Rebuild and compile the probe against the verified pinned source."""
    revision = revision_guard(upstream)
    subprocess.run(
        ["dune", "build", "--root", str(upstream), "p4spec/bin/main.exe"],
        check=True, cwd=ROOT,
    )
    build = upstream / "_build/default/p4spec/lib"
    SCRATCH.mkdir(parents=True, exist_ok=True)
    source = SCRATCH / "probe.ml"
    shutil.copyfile(ROOT / "test/type-runtime/probe.ml", source)
    command = [
        "ocamlfind", "ocamlopt", "-linkpkg", "-package",
        "core_unix.sys_unix,bignum.bigint,yojson,ppx_deriving_yojson.runtime,"
        "uucp,uuseg,uutf,str,menhirLib",
    ]
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
