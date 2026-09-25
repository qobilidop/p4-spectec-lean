#!/usr/bin/env bash
# Regenerate exports/<name>.al.json from the pinned, patched P4-SpecTec:
#   p4spectec algo -json <spec files>   (the AL: IL after the algo pass)
# Run from anywhere; paths inside the export are relative to the repository
# root, so the export is machine-independent. Requires the upstream build
# (scripts/build-upstream.sh, inside `nix develop .#upstream`).
#   scripts/export-spec.sh nano-p4 upstream/nano-p4-spec
#   scripts/export-spec.sh p4 upstream/p4-spectec/spec
# Upstream expands directories recursively in sorted order, excluding
# include/; use that same traversal for both flat and sectioned specs.
set -euo pipefail
root="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
name="${1:?usage: export-spec.sh <name> <spec dir>}"
dir="${2:?usage: export-spec.sh <name> <spec dir>}"
exe="$root/upstream/p4-spectec/_build/default/p4spec/bin/main.exe"
[ -x "$exe" ] || { echo "[export-spec] build upstream first: scripts/build-upstream.sh" >&2; exit 2; }
out="$root/exports/$name.al.json"
(cd "$root" && "$exe" algo -json "$dir" > "$out.tmp")
mv "$out.tmp" "$out"
python3 "$root/scripts/spec-snapshot.py" pack "$out"
echo "[export-spec] wrote $out ($(wc -c < "$out") bytes)"
