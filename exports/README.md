# Exports

Committed JSON produced by the pinned, patched P4-SpecTec build: the
contract between the OCaml frontend and the Lean side. Lean builds read
these files and need no OCaml. Regenerate with `scripts/export-spec.sh`
and `scripts/export-program.sh` inside `nix develop .#upstream` after
`scripts/build-upstream.sh`; CI checks that the generated Lean matches
them. Paths inside the exports are relative to the repository root.
Spec snapshots use deterministic gzip plus a SHA-256 of the original
JSON; program fixtures remain plain JSON. The gate verifies and extracts
both specs automatically, without OCaml. For direct tools, first run
`python3 scripts/spec-snapshot.py unpack exports/<name>.al.json`.
Extracted spec JSON is ignored. Tracked files must stay at or below 5 MiB.

- `nano-p4.al.json.gz`: the Nano-P4 specification's AL (the IL after
  upstream's algo pass), from `upstream/nano-p4-spec/*.watsup`. M1.
  244,303 compressed bytes; the extracted 8,508,087 bytes are unchanged
  from the original committed JSON. Migration preserves published history.
- `p4.al.json.gz`: the full P4 specification's AL from upstream's recursive
  `spec/` traversal, exported at M3A. 1,689 definitions, 98,387,720 bytes.
  It decodes and is covered by the capability census in the gate; a full
  generated Lean library is not yet available. Regenerate with
  `scripts/export-spec.sh p4 upstream/p4-spectec/spec`, which refreshes
  deterministic gzip and the raw SHA-256 in `p4.al.json.sha256`.
  Unpack with `python3 scripts/spec-snapshot.py unpack exports/p4.al.json`
  (the gate does this automatically). Extraction verifies the checksum
  before replacing the ignored `p4.al.json`. The archive is 2.61 MiB;
  no source information is removed.
- `programs/nano-p4/<dir>/<name>.json`: upstream's Nano-P4 corpus, booted
  by the nano frontend, one IL value per program, next to the oracle the
  differential harness compares against: `<name>.verdict`, the AL
  interpreter's `Program_ok` verdict (`pass` or `fail`); on success
  `<name>.outputs.json`, its output values (the typing context); on
  failure `<name>.diagnostic`, the first 400 bytes of its diagnostic; and
  `<name>.verdict.sl`, the SL interpreter's verdict for comparison.
