#!/usr/bin/env bash
# Regenerate P4SpecTec/Codegen/Keywords.lean from Lean's token table.
# With --check, fail if the committed file differs.
set -euo pipefail
root="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
out="$root/P4SpecTec/Codegen/Keywords.lean"
tmp="$(mktemp)"
(cd "$root" && lake env lean scripts/gen-keywords.lean) > "$tmp"
if [ "${1:-}" = "--check" ]; then
  if ! diff -q "$out" "$tmp" >/dev/null; then
    echo "[gen-keywords] $out is stale; run scripts/gen-keywords.sh" >&2; rm -f "$tmp"; exit 1
  fi
  rm -f "$tmp"
else
  mv "$tmp" "$out"
fi
