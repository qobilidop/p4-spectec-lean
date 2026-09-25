#!/usr/bin/env python3
"""Rung 2, typing leg: compare the generated `Program_ok.run` and the Lean
port of the AL interpreter with upstream.

For every booted program under exports/programs/nano-p4/, the AL
interpreter's verdict (`<name>.verdict`, recorded by scripts/export-program.sh
from `nano-p4spectec check -il`) is compared with the verdicts of two Lean
executables on the same program: `lake exe nano-p4-run` (the generated
executable typing relation) and `lake exe nano-p4-interp` (the trusted
interpreter port, on the deep term against the AL export). Both compare
the output typing context with the one upstream recorded
(`<name>.outputs.json`). Exit 0 only when every program agrees on both
legs. A program the frontend rejected (`<name>.unparseable`) has no
verdict and is skipped. The SL interpreter's verdict (`<name>.verdict.sl`)
is reported when it differs from the AL's, for information. With
`P4SPECTEC_INTERP_DEBUG` set, the interpreter traces every invocation.

    test/diff/run.py            # all of the corpus, both legs
    test/diff/run.py positive   # one subdirectory
    test/diff/run.py --leg run  # one leg (`run` or `interp`)
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
CORPUS = ROOT / "exports" / "programs" / "nano-p4"


def leg(exe, programs, paths):
    """Run one executable on the programs; the number of disagreements."""
    run = subprocess.run(["lake", "exe", exe, *paths], cwd=ROOT,
                         capture_output=True, text=True)
    if run.returncode != 0:
        sys.stderr.write(run.stderr)
        print(f"{exe} failed with exit {run.returncode}")
        return len(programs)
    lean = {}
    for line in run.stdout.splitlines():
        if " " in line:
            path, verdict = line.rsplit(" ", 1)
            lean[path] = verdict
    agree = disagree = 0
    for (path, expected), rel in zip(programs, paths):
        got = lean.get(rel, "missing")
        if got == expected:
            agree += 1
        else:
            disagree += 1
            print(f"DISAGREE [{exe}] {rel}: upstream (AL) {expected}, lean {got}")
    print(f"[diff {exe}] {agree} agree, {disagree} disagree, {len(programs)} programs")
    return disagree


def main(argv):
    legs = ["nano-p4-run", "nano-p4-interp"]
    if "--leg" in argv:
        i = argv.index("--leg")
        legs = ["nano-p4-" + argv[i + 1]]
        argv = argv[:i] + argv[i + 2:]
    subdirs = argv or sorted(p.name for p in CORPUS.iterdir() if p.is_dir())
    programs = []
    for sub in subdirs:
        for verdict in sorted((CORPUS / sub).glob("*.verdict")):
            programs.append((verdict.with_suffix(".json"), verdict.read_text().strip()))
    if not programs:
        print("no programs with verdicts under", CORPUS)
        return 2
    paths = [str(p.relative_to(ROOT)) for p, _ in programs]
    disagree = sum(leg(exe, programs, paths) for exe in legs)
    for (path, expected), rel in zip(programs, paths):
        sl = path.with_suffix(".verdict.sl")
        if sl.exists() and sl.read_text().strip() != expected:
            print(f"NOTE {rel}: upstream SL says {sl.read_text().strip()}, AL says {expected}")
    with_outputs = sum(1 for p, _ in programs if p.with_suffix(".outputs.json").exists())
    print(f"[diff] {len(programs)} programs, {with_outputs} with output values compared, "
          f"{disagree} disagreement(s) over {len(legs)} leg(s)")
    return 0 if disagree == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
