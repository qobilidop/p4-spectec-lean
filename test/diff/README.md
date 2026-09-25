# Differential-testing harness

Rung 2 of `docs/design.md` section 5: run the generated executable
relations and upstream's interpreter on the same corpus and compare.

- `run.py`: the typing leg. For every exported program under
  `exports/programs/nano-p4/`, compares the AL interpreter's recorded
  verdict with `lake exe nano-p4-run`, which decodes the program into the
  generated `program` type, runs the generated `Program_ok.run`, compares
  the output typing context with the one upstream recorded, and reports
  fuel exhaustion apart from rejection. Exit 0 only when every program
  agrees. Part of `scripts/check.sh`. The oracle is the AL interpreter
  because that is the one the port mirrors (the SL interpreter's verdict
  is recorded beside it and reported when it differs).
- The packet leg (nano-switch simulation against STF files) arrives with
  the target instance in M3.

The harness is Python (design section 12, decided at M1): it only
orchestrates and compares; the Lean side is `P4SpecTecTest/Diff/NanoP4Run.lean`.
