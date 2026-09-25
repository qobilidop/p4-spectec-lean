# Patches to P4-SpecTec

Applied by `scripts/build-upstream.sh` to the submodule at its pinned
commit, in name order. Each patch is small, touches nothing the upstream
commands run, and is meant to be offered upstream.

Planned:

- `0001-json-export.patch`: `elab --json` prints the elaborated IL using
  the JSON serializers `ast.ml` already derives; `run --dump-value` prints
  a booted program's IL value the same way.
