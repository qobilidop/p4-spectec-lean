# Patches to P4-SpecTec

Applied by `scripts/build-upstream.sh` to the submodule at its pinned
commit, in name order, with `git apply` (idempotent: a patch whose reverse
applies is skipped). Each patch is small, touches nothing the upstream
commands run, and is meant to be offered upstream.

- `0001-json-export.patch`: `elab -json` prints the elaborated IL and
  `algo -json` the AL (the IL after the algo pass, what the AL interpreter
  runs and what this compiler consumes) using the JSON serializers the
  ASTs already derive; `def` and `spec` gain the `[@@deriving yojson]` the
  other types have. `nano-p4spectec parse -json` prints a booted Nano-P4
  program's IL value the same way.

The patch is regenerated from the submodule's working tree with
`git -C upstream/p4-spectec diff > upstream/patches/0001-json-export.patch`.
