#!/usr/bin/env bash
# Text hygiene for tracked source and documentation: no trailing whitespace,
# a final newline, Lean lines at most 100 characters (URLs excepted), and no
# bare `import Lean` (import the modules actually used).
set -euo pipefail
root="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
fail=0
files=$(git -C "$root" ls-files -- '*.lean' '*.md' '*.sh' '*.toml' '*.nix' '*.yml')
for f in $files; do
  p="$root/$f"
  if grep -nE '[[:space:]]+$' "$p" >/dev/null; then
    echo "[check-text] trailing whitespace: $f"; grep -nE '[[:space:]]+$' "$p" | head -3; fail=1
  fi
  if [ -s "$p" ] && [ "$(tail -c1 "$p" | od -An -c | tr -d ' ')" != '\n' ]; then
    echo "[check-text] no final newline: $f"; fail=1
  fi
done
for f in $(git -C "$root" ls-files -- '*.lean'); do
  p="$root/$f"
  if grep -nvE 'https?://' "$p" | awk -F: 'length($0) - length($1) - 1 > 100 {print; found=1} END {exit !found}' >/dev/null; then
    echo "[check-text] line over 100 characters: $f"; fail=1
  fi
  if grep -nE '^import Lean$' "$p" >/dev/null; then
    echo "[check-text] bare 'import Lean': $f"; fail=1
  fi
done
exit "$fail"
