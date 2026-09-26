#!/usr/bin/env python3
"""Boot one full-P4 program and record two independent pinned AL sessions."""

import argparse
import gzip
import json
import os
from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[1]
PROBE = ROOT / "test/p4-oracle/probe.ml"
SCRATCH = ROOT / ".artifacts/p4-oracle"
PATCH = "upstream/patches/0001-json-export.patch"
PATCHED_FILES = (
    "p4spec/bin/main.ml", "p4spec/bin/nano.ml",
    "p4spec/lib/lang/al/ast.ml", "p4spec/lib/lang/il/ast.ml",
)
LIBRARIES = [
    ("util", "util"), ("cache", "cache"), ("domain", "domain"),
    ("diagnostic", "diagnostic"), ("lang", "lang"),
    ("frontend", "frontend"),
    ("runtime/error_runtime", "error_runtime"),
    ("runtime/type", "type"), ("runtime/value", "value"),
    ("runtime/dynamic-runner", "dynamic_runner"),
    ("runtime/dynamic", "dynamic"),
    ("runtime/dynamic-al", "dynamic_al"),
    ("runtime/dynamic-sl", "dynamic_sl"),
    ("runtime/dynamic-pl", "dynamic_pl"),
    ("runtime/static", "static"), ("runtime/prose", "prose"),
    ("runtime/sim", "sim"), ("runtime", "runtime"),
    ("interface/builtin", "builtin"), ("pass", "pass"),
    ("interface/nano", "nano"), ("interface/p4", "p4"),
    ("interface/spectec", "spectec"), ("interface", "interface"),
    ("coverage/instr", "instr"),
    ("coverage/dangling", "dangling"),
    ("interp/inst", "inst"),
    ("interp/interp-common", "interp_common"),
    ("interp/interp-al", "interp_al"),
    ("interp/interp-sl", "interp_sl"),
    ("interp/interp-pl", "interp_pl"), ("interp", "interp"),
    ("runner", "runner"), ("stf", "stf"),
    ("coverage", "coverage"),
    ("backend-sim", "backend_sim"),
]


def revision_guard(upstream: Path) -> str:
    entry = subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-files", "--stage", "--", "upstream/p4-spectec"],
        text=True,
    ).split()
    revision = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True,
    ).strip()
    root = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "--show-toplevel"],
        text=True,
    ).strip()
    if root != str(upstream) or len(entry) != 4 or entry[:2] != ["160000", revision]:
        raise SystemExit("upstream must be a repository root at the indexed gitlink pin")
    expected_patch = subprocess.check_output(
        ["git", "-C", str(ROOT), "show", f"HEAD:{PATCH}"])
    actual_patch = subprocess.check_output(
        ["git", "-C", str(upstream), "diff", "HEAD", "--no-ext-diff",
         "--no-color", "--binary"])
    status = subprocess.check_output(
        ["git", "-C", str(upstream), "status", "--short", "--untracked-files=all"],
        text=True,
    ).splitlines()
    if actual_patch != expected_patch or status != [f" M {path}" for path in PATCHED_FILES]:
        raise SystemExit("upstream source differs from the exact committed export patch")
    return revision


def compile_probe(upstream: Path) -> Path:
    if subprocess.run(["dune", "build", "p4spec/bin/main.exe"],
                      cwd=upstream).returncode != 0:
        raise SystemExit("failed to rebuild pinned upstream source")
    build = upstream / "_build/default/p4spec/lib"
    workspace = SCRATCH / str(os.getpid())
    workspace.mkdir(parents=True, exist_ok=True)
    source = workspace / "probe.ml"
    shutil.copyfile(PROBE, source)
    command = [
        "ocamlfind", "ocamlopt", "-linkpkg", "-package",
        "core,core_unix,core_unix.sys_unix,bignum.bigint,yojson,"
        "ppx_deriving_yojson.runtime,uucp,uuseg,uutf,str,menhirLib",
    ]
    for directory, name in LIBRARIES:
        objects = build / directory / f".{name}.objs"
        command += ["-I", str(objects / "byte"), "-I", str(objects / "native")]
    command += [str(build / directory / f"{name}.cmxa") for directory, name in LIBRARIES]
    executable = workspace / "probe"
    command += [str(source), "-o", str(executable)]
    if subprocess.run(command, cwd=ROOT).returncode != 0:
        raise SystemExit("failed to compile pinned full-P4 AL oracle probe")
    return executable


def source_region(value) -> bool:
    return (isinstance(value, dict) and set(value) == {"left", "right"}
            and all(isinstance(value[side], dict)
                    and set(value[side]) == {"file", "line", "column"}
                    and isinstance(value[side]["file"], str)
                    and type(value[side]["line"]) is int
                    and type(value[side]["column"]) is int
                    for side in ("left", "right")))


def typed_value(value) -> bool:
    return (isinstance(value, dict) and set(value) == {"it", "note", "at"}
            and isinstance(value["it"], list)
            and isinstance(value["note"], dict)
            and set(value["note"]) == {"vid", "typ", "vhash"}
            and type(value["note"]["vid"]) is int
            and isinstance(value["note"]["typ"], list)
            and type(value["note"]["vhash"]) is int
            and source_region(value["at"]))


def diagnostic(value) -> bool:
    return (isinstance(value, dict)
            and set(value) == {"source", "code", "message", "region"}
            and isinstance(value["source"], str)
            and (value["code"] is None or isinstance(value["code"], str))
            and isinstance(value["message"], str)
            and isinstance(value["region"], str))


def validate_run(run, relation: str) -> None:
    fields = {"relation", "mode", "cache", "det", "guard", "counterBefore",
              "counterAfterBoot", "counterAfter", "boot", "result"}
    if not isinstance(run, dict) or set(run) != fields:
        raise SystemExit(f"malformed {relation} probe envelope")
    if (run["relation"] != relation or run["mode"] != "AL"
            or run["cache"] is not True or run["det"] is not False
            or run["guard"] is not False):
        raise SystemExit(f"unexpected {relation} probe mode or configuration")
    if (type(run["counterBefore"]) is not int or run["counterBefore"] != 0
            or type(run["counterAfterBoot"]) is not int
            or type(run["counterAfter"]) is not int):
        raise SystemExit(f"malformed {relation} fresh-counter state")
    result = run["result"]
    if not isinstance(result, dict) or result.get("class") not in (
            "pass", "syntax", "unmatch", "abort"):
        raise SystemExit(f"malformed {relation} result class")
    result_class = result["class"]
    if result_class == "pass":
        if (not typed_value(run["boot"]) or set(result) != {"class", "outputs"}
                or not isinstance(result["outputs"], list)
                or not all(typed_value(value) for value in result["outputs"])):
            raise SystemExit(f"malformed {relation} pass result")
    elif result_class == "syntax":
        if (run["boot"] is not None or set(result) != {"class", "diagnostic"}
                or not diagnostic(result["diagnostic"])):
            raise SystemExit(f"malformed {relation} syntax result")
    elif (not typed_value(run["boot"]) or set(result) != {"class", "diagnostic"}
          or not diagnostic(result["diagnostic"])):
        raise SystemExit(f"malformed {relation} failure result")


def observe(executable: Path, spec: Path, includes: Path, program: Path) -> dict:
    runs = {}
    for relation in ("Program_ok", "Program_inst"):
        stdout = subprocess.check_output(
            [str(executable), str(spec), str(includes), str(program), relation],
            text=True, cwd=ROOT,
        )
        runs[relation] = json.loads(stdout)
        validate_run(runs[relation], relation)
    if runs["Program_ok"]["boot"] != runs["Program_inst"]["boot"]:
        raise SystemExit("independent relation processes produced different boot values")
    return {"boot": runs["Program_ok"]["boot"],
            "relations": {key: {k: v for k, v in run.items() if k != "boot"}
                          for key, run in runs.items()}}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", required=True, type=Path)
    parser.add_argument("--includes", required=True, type=Path)
    parser.add_argument("--program", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    for path in (args.upstream, args.includes, args.program, args.output):
        if not path.is_absolute():
            parser.error("all paths must be absolute")
    if args.output.suffix != ".gz":
        parser.error("--output must end in .gz")
    upstream = args.upstream.resolve()
    revision = revision_guard(upstream)
    if not args.includes.is_dir() or not args.program.is_file():
        parser.error("include directory and program must exist")
    executable = compile_probe(upstream)
    observation = observe(executable, upstream / "spec", args.includes, args.program)
    result = {"schemaVersion": 1, "upstreamRevision": revision,
              "program": str(args.program), "observation": observation}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_name(args.output.name + f".{os.getpid()}.tmp")
    with temporary.open("wb") as output:
        with gzip.GzipFile(filename="", mode="wb", fileobj=output, mtime=0) as packed:
            packed.write(json.dumps(result, ensure_ascii=True, separators=(",", ":"))
                         .encode("utf-8"))
    temporary.replace(args.output)
    print(f"[p4-oracle] {args.program.name}: " + ", ".join(
        f"{name}={run['result']['class']}@{run['counterAfter']}"
        for name, run in observation["relations"].items()))


if __name__ == "__main__":
    main()
