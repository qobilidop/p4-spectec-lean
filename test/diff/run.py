#!/usr/bin/env python3
"""Rung 2, typing leg: compare the generated `Program_ok.run` with upstream.

For every booted program under exports/programs/nano-p4/, the AL
interpreter's verdict (`<name>.verdict`, recorded by scripts/export-program.sh
from `nano-p4spectec check -il`) is compared with the verdict of
`lake exe nano-p4-run` on the same program, which also compares the output
typing context with the one upstream recorded (`<name>.outputs.json`) and
reports fuel exhaustion apart from rejection. Exit 0 only when every program
agrees. A program the frontend rejected (`<name>.unparseable`) has no
verdict and is skipped. The SL interpreter's verdict (`<name>.verdict.sl`)
is reported when it differs from the AL's, for information.

    test/diff/run.py            # all of the corpus
    test/diff/run.py positive   # one subdirectory
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
CORPUS = ROOT / "exports" / "programs" / "nano-p4"


def main(argv):
    subdirs = argv or sorted(p.name for p in CORPUS.iterdir() if p.is_dir())
    programs = []
    for sub in subdirs:
        for verdict in sorted((CORPUS / sub).glob("*.verdict")):
            programs.append((verdict.with_suffix(".json"), verdict.read_text().strip()))
    if not programs:
        print("no programs with verdicts under", CORPUS)
        return 2
    paths = [str(p.relative_to(ROOT)) for p, _ in programs]
    run = subprocess.run(["lake", "exe", "nano-p4-run", *paths], cwd=ROOT,
                         capture_output=True, text=True)
    if run.returncode != 0:
        sys.stderr.write(run.stderr)
        print("nano-p4-run failed with exit", run.returncode)
        return 2
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
            print(f"DISAGREE {rel}: upstream (AL) {expected}, lean {got}")
        sl = path.with_suffix(".verdict.sl")
        if sl.exists() and sl.read_text().strip() != expected:
            print(f"NOTE {rel}: upstream SL says {sl.read_text().strip()}, AL says {expected}")
    with_outputs = sum(1 for p, _ in programs if p.with_suffix(".outputs.json").exists())
    print(f"[diff] {agree} agree, {disagree} disagree, {len(programs)} programs, "
          f"{with_outputs} with output values compared")
    return 0 if disagree == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
