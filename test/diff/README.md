# Differential-testing harness

Rung 2 of `docs/design.md` section 5: run the generated executable
relations and upstream's interpreter on the same corpus and compare.

- `run.py`: the typing leg, in two legs. For every exported program
  under `exports/programs/nano-p4/`, it compares the AL interpreter's
  recorded verdict with two runs: `lake exe nano-p4-run` decodes the
  program into the generated `program` type and runs the generated
  `Program_ok.run`; `lake exe nano-p4-interp` runs `Program_ok` through
  the Lean port of the AL interpreter on the exported AL. Each compares
  the output typing context with the one upstream recorded, and reports
  divergence (the interpreter port's fuel running out) apart from
  rejection. Exit 0 only when every program agrees on both legs;
  `--leg run|interp` runs one. Part of `scripts/check.sh`. The oracle is the AL interpreter
  because that is the one the port mirrors (the SL interpreter's verdict
  is recorded beside it and reported when it differs).
- The packet leg (nano-switch simulation against STF files) arrives with
  the target instance in M3.

The harness is Python (design section 12, decided at M1): it only
orchestrates and compares; the Lean side is
`P4SpecTecTest/Diff/NanoP4Run/Main.lean` and
`P4SpecTecTest/Diff/NanoP4Interp/Main.lean`.
