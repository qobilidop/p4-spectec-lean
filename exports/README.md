# Exports

Committed JSON produced by the pinned, patched P4-SpecTec build: the
contract between the OCaml frontend and the Lean side. Lean builds read
these files and need no OCaml. Regenerate with `scripts/export-spec.sh`
and `scripts/export-program.sh` inside `nix develop .#upstream` after
`scripts/build-upstream.sh`; CI checks that the generated Lean matches
them. Paths inside the exports are relative to the repository root.

- `nano-p4.al.json`: the Nano-P4 specification's AL (the IL after
  upstream's algo pass), from `upstream/nano-p4-spec/*.watsup`. M1.
- `p4.al.json`: the full P4 specification's AL. M3, not yet exported.
- `programs/nano-p4/<dir>/<name>.json`: upstream's Nano-P4 corpus, booted
  by the nano frontend, one IL value per program, next to the oracle the
  differential harness compares against: `<name>.verdict`, the AL
  interpreter's `Program_ok` verdict (`pass` or `fail`); on success
  `<name>.outputs.json`, its output values (the typing context); on
  failure `<name>.diagnostic`, the first 400 bytes of its diagnostic; and
  `<name>.verdict.sl`, the SL interpreter's verdict for comparison.
