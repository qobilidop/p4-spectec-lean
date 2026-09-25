#!/usr/bin/env bash
# Every module under a library directory is imported by that library's root,
# so `lake build` elaborates every file and no proof or test is silently
# skipped. Usage: scripts/check-imports.sh <Root> [<Root> ...]
set -euo pipefail
root="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
fail=0
for lib in "$@"; do
  dir="$root/$lib"
  file="$root/$lib.lean"
  [ -d "$dir" ] || continue
  while IFS= read -r path; do
    case "$path" in */Main.lean) continue ;; esac   # executable roots are not library modules
    mod="${path#"$root"/}"; mod="${mod%.lean}"; mod="${mod//\//.}"
    if ! grep -qE "^(public )?import $mod\$" "$file"; then
      echo "[check-imports] $file does not import $mod"; fail=1
    fi
  done < <(find "$dir" -name '*.lean' | sort)
done
exit "$fail"
