#!/usr/bin/env python3
"""Boot one full-P4 program and record two independent pinned AL sessions."""

import argparse
import gzip
import json
import os
from pathlib import Path
import sys
import subprocess


ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts"))
PROBE = ROOT / "P4SpecTecTest/Oracle/P4/Replay/probe.ml"
SCRATCH = ROOT / ".artifacts/p4-oracle"
from oracle_build import (LIBRARIES, PATCH, PATCHED_FILES, revision_guard,
                          validate_probe_workspace)
import oracle_build


def compile_probe(upstream: Path, workspace_key: str | None = None, *,
                  probe: Path = PROBE, scratch: Path = SCRATCH) -> Path:
    """Build a full-P4 probe, with explicit suite-local source and cache paths."""
    return oracle_build.compile_probe(upstream, probe=probe, scratch=scratch,
                                      workspace_key=workspace_key)


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
