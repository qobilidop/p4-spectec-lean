#!/usr/bin/env bash
# Build P4-SpecTec at the pinned submodule commit with our patches applied,
# inside `nix develop .#upstream`, and print the built executables.
#
# Patches under upstream/patches/*.patch are applied in name order to the
# submodule's working tree with `git apply`; a patch already applied (its
# reverse applies cleanly) is skipped, so the script is idempotent. The
# submodule's recorded commit never changes; `git -C upstream/p4-spectec
# checkout -- .` removes the patches again.
set -euo pipefail
root="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
up="$root/upstream/p4-spectec"

for patch in "$root"/upstream/patches/*.patch; do
  [ -e "$patch" ] || continue
  if git -C "$up" apply --reverse --check "$patch" 2>/dev/null; then
    echo "[build-upstream] already applied: $(basename "$patch")"
  else
    git -C "$up" apply "$patch"
    echo "[build-upstream] applied: $(basename "$patch")"
  fi
done

if ! command -v dune >/dev/null 2>&1; then
  echo "[build-upstream] dune not on PATH; run inside 'nix develop .#upstream'" >&2
  exit 2
fi
# Upstream's Makefile removes stale generated parser files before building.
rm -f "$up/p4spec/lib/parsing/parser.ml" "$up/p4spec/lib/parsing/parser.mli"
(cd "$up/p4spec" && dune build bin/main.exe bin/nano.exe 2>&1 | grep -v -e trigraph -e '^ *[0-9]* |' -e '^ *|' -e 'warning generated' || true)
for exe in main nano; do
  [ -x "$up/_build/default/p4spec/bin/$exe.exe" ] || { echo "[build-upstream] $exe.exe missing" >&2; exit 1; }
done
echo "$up/_build/default/p4spec/bin/main.exe"
echo "$up/_build/default/p4spec/bin/nano.exe"
