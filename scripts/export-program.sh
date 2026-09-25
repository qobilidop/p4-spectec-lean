#!/usr/bin/env bash
# Boot Nano-P4 programs through P4-SpecTec's nano frontend and write their
# IL values as JSON under exports/programs/<name>/, next to upstream's
# typing verdict (`pass` or `fail` from `nano-p4spectec check`) as the
# oracle the differential harness compares against:
#   nano-p4spectec parse -json -i <includes> -p <file>.p4
#   nano-p4spectec check <spec> -i <includes> -p <file>.p4
# Requires the upstream build (scripts/build-upstream.sh). With no
# arguments, exports upstream's whole Nano-P4 corpus.
#   scripts/export-program.sh [<dir> ...]
set -euo pipefail
root="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
up="$root/upstream/p4-spectec"
exe="$up/_build/default/p4spec/bin/nano.exe"
[ -x "$exe" ] || { echo "[export-program] build upstream first: scripts/build-upstream.sh" >&2; exit 2; }
# Paths are passed relative to the repository root so the regions inside the
# export are machine-independent.
includes="upstream/p4-spectec/nano-p4/include"
dirs=("$@")
if [ "${#dirs[@]}" -eq 0 ]; then
  dirs=(upstream/p4-spectec/nano-p4/testdata/positive upstream/p4-spectec/nano-p4/testdata/negative
        upstream/p4-spectec/nano-p4/testdata/exercise)
fi
count=0
for dir in "${dirs[@]}"; do
  sub="$(basename "$dir")"
  outdir="$root/exports/programs/nano-p4/$sub"
  mkdir -p "$outdir"
  for p4 in "$root/$dir"/*.p4; do
    [ -e "$p4" ] || continue
    base="$(basename "$p4" .p4)"
    if (cd "$root" && "$exe" parse -json -i "$includes" -p "$dir/$base.p4" > "$outdir/$base.json.tmp" 2>/dev/null); then
      mv "$outdir/$base.json.tmp" "$outdir/$base.json"
      if (cd "$root" && "$exe" check upstream/nano-p4-spec/*.watsup -i "$includes" -p "$dir/$base.p4" >/dev/null 2>&1); then
        echo pass > "$outdir/$base.verdict"
      else
        echo fail > "$outdir/$base.verdict"
      fi
    else
      # a program the frontend rejects has no value; record that
      rm -f "$outdir/$base.json.tmp"
      echo "unparseable" > "$outdir/$base.unparseable"
    fi
    count=$((count + 1))
  done
done
echo "[export-program] processed $count programs"
