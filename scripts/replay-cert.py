#!/usr/bin/env python3
"""Replay generated certificate modules against the current tactics, fast.

A tactic change invalidates every generated certificate, so `lake build` of one
certificate first rebuilds its whole dependency chain. Certificate *statements* do
not depend on the tactics, so for iteration it is enough to rebuild the `P4SpecTec`
library and re-elaborate a scratch copy of the module against the existing `.olean`
files of its generated imports. The copy lives under `.artifacts/replay/`; it can
keep only selected theorems and add heartbeat, trace and printing options.

This is a development aid, never evidence. It is faithful only when the change is
confined to tactic modules: imported generated modules keep their earlier proofs,
and their object files predate any regenerated statement or rebuilt non-tactic
`P4SpecTec` module (`Prelude`, `Refine`, `Interp`) they were compiled against. After
such changes build the affected modules first. `lake build --wfail` and
`scripts/check.sh` remain the verdict.

    scripts/replay-cert.py NanoP4Spec.Refinement.Decl_load --only refines \\
        --heartbeats 400000 --trace
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".artifacts/replay"
DECLARATION = re.compile(r"^(?:private )?(?:theorem|def|instance) ([^\s:({\[]+)")
AUDIT = re.compile(r"^#audit_axioms (\S+)")
BUDGET = re.compile(r"^set_option maxHeartbeats \d+ in$")


def module_path(target):
    """A dotted module name or a path to its source file."""
    path = Path(target)
    if path.suffix == ".lean":
        return path if path.is_absolute() else ROOT / path
    return ROOT / (target.replace(".", "/") + ".lean")


def chunks(text):
    """Split at blank lines followed by a column-0 line; a chunk keeps its docstring."""
    parts, current = [], []
    for line in text.splitlines(keepends=True):
        if current and line.strip() and not line[0].isspace() and not current[-1].strip():
            parts.append("".join(current))
            current = []
        current.append(line)
    if current:
        parts.append("".join(current))
    return parts


def chunk_kind(chunk):
    """Classify a chunk: `("theorem", name)`, `("audit", name)` or `("other", None)`.
    Names are as written (`«$add_map».dispatch`, `NanoP4Spec.R.refines` for an audit)."""
    for line in chunk.splitlines():
        if line.startswith("/--") or line.startswith("  ") or not line.strip():
            continue
        if BUDGET.match(line):
            continue
        declared = DECLARATION.match(line)
        if declared and line.removeprefix("private ").startswith("theorem"):
            return "theorem", declared.group(1)
        audited = AUDIT.match(line)
        if audited:
            return "audit", audited.group(1)
        return "other", None
    return "other", None


def mentions(text, name):
    """Whether `name` occurs in `text` as a whole identifier."""
    return re.search(r"(?<![\w'.»])" + re.escape(name) + r"(?![\w'»])", text) is not None \
        or re.search(r"\." + re.escape(name) + r"(?![\w'»])", text) is not None


def select(text, only):
    """Keep every non-theorem chunk, the theorems whose full name contains a selected
    word, any other theorem a kept chunk refers to (transitively), and the audits of
    kept theorems."""
    if not only:
        return text
    parts = [(chunk, *chunk_kind(chunk)) for chunk in chunks(text)]
    kept = {i for i, (_, kind, name) in enumerate(parts)
            if kind == "other" or (kind == "theorem" and any(w in name for w in only))}
    changed = True
    while changed:
        changed = False
        body = "".join(parts[i][0] for i in kept)
        for i, (_, kind, name) in enumerate(parts):
            if i not in kept and kind == "theorem" and mentions(body, name):
                kept.add(i)
                changed = True
    theorems = [parts[i][2] for i in kept if parts[i][1] == "theorem"]
    for i, (_, kind, name) in enumerate(parts):
        if kind == "audit" and any(name == t or name.endswith("." + t) for t in theorems):
            kept.add(i)
    return "".join(parts[i][0] for i in sorted(kept))


def options(heartbeats, trace, full_terms):
    """The `set_option` lines selected on the command line."""
    lines = []
    if heartbeats is not None:
        lines.append(f"set_option maxHeartbeats {heartbeats}")
    if trace:
        lines.append("set_option refine_al.trace true")
    if full_terms:
        lines += ["set_option pp.deepTerms true", "set_option pp.maxSteps 10000000"]
    return lines


def instrument(text, extra):
    """Insert the options after the last preamble `set_option` (before the first `open`
    or `namespace`), which they override. A per-theorem heartbeat budget is dropped when
    the heartbeat limit is overridden; other scoped options are left alone."""
    if not extra:
        return text
    lines = text.splitlines(keepends=True)
    if any(line.startswith("set_option maxHeartbeats ") for line in extra):
        lines = [line for line in lines if not BUDGET.match(line.rstrip("\n"))]
    body = next((i for i, line in enumerate(lines)
                 if line.startswith("open ") or line.startswith("namespace ")), len(lines))
    last = max((i for i, line in enumerate(lines[:body]) if line.startswith("set_option ")),
               default=None)
    if last is None:
        raise ValueError("generated module has no set_option preamble")
    return "".join(lines[:last + 1] + [line + "\n" for line in extra] + lines[last + 1:])


def imports(text):
    """The imported module names."""
    return [line.split()[1] for line in text.splitlines() if line.startswith("import ")]


def missing_imports(text):
    """Generated imports without an object file. Lake's traces hash all inputs together,
    so a present object file may still predate a regenerated statement or a rebuilt
    non-tactic module (see the module docstring); build those modules first."""
    missing = []
    for module in imports(text):
        if module.startswith("P4SpecTec."):
            continue
        if not (ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")).exists():
            missing.append(module)
    return missing


def replay(source, args):
    """Write the instrumented scratch copy of `source` and elaborate it; return the result."""
    text = source.read_text()
    scratch = OUT / source.relative_to(ROOT)
    scratch.parent.mkdir(parents=True, exist_ok=True)
    scratch.write_text(instrument(select(text, args.only),
                                  options(args.heartbeats, args.trace, args.full_terms)))
    log = scratch.with_suffix(".log")
    started = time.monotonic()
    with log.open("w") as out:
        code = subprocess.run(["lake", "env", "lean", str(scratch)], cwd=ROOT,
                              stdout=out, stderr=subprocess.STDOUT).returncode
    return source, code, time.monotonic() - started, log


def main(argv=None):
    """Rebuild the tactic library, then replay each module; exit 1 if any fails."""
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("modules", nargs="+", help="dotted module names or .lean paths")
    parser.add_argument("--only", action="append", default=[],
                        help="keep theorems whose full name contains this text (repeatable), "
                        "and the theorems and definitions they refer to")
    parser.add_argument("--heartbeats", type=int, help="override maxHeartbeats to fail fast")
    parser.add_argument("--trace", action="store_true", help="enable refine_al.trace")
    parser.add_argument("--full-terms", action="store_true", help="print terms unabridged")
    parser.add_argument("--jobs", type=int, default=4, help="modules replayed in parallel")
    parser.add_argument("--no-build", action="store_true",
                        help="skip rebuilding the P4SpecTec library first")
    args = parser.parse_args(argv)
    sources = [module_path(m) for m in args.modules]
    for source in sources:
        if not source.exists():
            parser.error(f"no source file {source}")
    if not args.no_build:
        built = subprocess.run(["lake", "build", "P4SpecTec"], cwd=ROOT,
                               capture_output=True, text=True)
        if built.returncode != 0:
            print(built.stdout[-4000:] + built.stderr[-4000:])
            print("[replay] lake build P4SpecTec failed", file=sys.stderr)
            return 1
    missing = sorted({m for s in sources for m in missing_imports(s.read_text())})
    if missing:
        print("[replay] missing object files; run: lake build " + " ".join(missing),
              file=sys.stderr)
        return 1
    failed = 0
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for source, code, seconds, log in pool.map(lambda s: replay(s, args), sources):
            status = "ok" if code == 0 else "FAILED"
            print(f"[replay] {status} {source.relative_to(ROOT)} ({seconds:.1f}s) log: "
                  f"{log.relative_to(ROOT)}")
            if code != 0:
                failed += 1
                errors = [line for line in log.read_text().splitlines()
                          if ": error" in line]
                for line in errors[:10]:
                    print(f"  {line[:240]}")
                if any("object file" in line for line in errors):
                    print(f"  hint: a transitive import is unbuilt; run: lake build "
                          f"{'.'.join(source.relative_to(ROOT).with_suffix('').parts)}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
