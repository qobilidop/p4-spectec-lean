# Exports

Committed JSON produced by the pinned P4-SpecTec build: the contract
between the OCaml frontend and the Lean side. Lean builds read these
files and need no OCaml. Regenerate with `scripts/export-spec.sh` and
`scripts/export-program.sh`; CI checks they are current.

- `nano-p4.il.json`: the Nano-P4 specification's elaborated IL (M1).
- `p4.il.json`: the full P4 specification's elaborated IL (M3).
- `programs/`: booted P4 programs used by Lean tests.
