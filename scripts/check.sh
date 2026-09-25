#!/usr/bin/env bash
# Every gate CI runs. Exit 0 is the only passing verdict.
#
# 1. Layout the design and AGENTS.md rely on; no CLAUDE.md; docs/ does not
#    link into .agents/.
# 2. Text hygiene (scripts/check-text.sh).
# 3. Every module is imported by its library root (scripts/check-imports.sh).
# 4. Mirror checks: mirrored modules have upstream's constructors in
#    upstream's order (scripts/check-mirror.py).
# 5. Lean: `lake build --wfail` (warnings fail, and a `sorry` is a warning),
#    then `lake test`.
# 6. Generated code is current: the keyword table matches the toolchain and
#    the committed NanoP4Spec/ is byte-identical to what the generator
#    writes from exports/nano-p4.al.json.
# 7. Rung 2: the generated typing relation agrees with upstream's verdict on
#    every exported Nano-P4 program (test/diff/run.py).
# A missing lake is a failure, not a skip, unless P4SPECTEC_SKIP_LEAN=1 says
# so explicitly.
set -euo pipefail
root="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
fail=0

say() { printf '[check] %s\n' "$*"; }

for path in \
  AGENTS.md README.md LICENSE docs/design.md \
  .agents/status.md .agents/decisions.md .agents/roadmap.md \
  lakefile.toml lake-manifest.json lean-toolchain \
  P4SpecTec.lean P4SpecTecTest.lean P4Lib.lean NanoP4Spec.lean P4Spec.lean \
  P4SpecTec/Codegen/Main.lean P4SpecTec/Codegen/Keywords.lean \
  upstream/p4-spectec/README.md upstream/nano-p4-spec/README.md \
  upstream/patches/0001-json-export.patch \
  exports/nano-p4.al.json exports/programs/nano-p4 \
  scripts/build-upstream.sh scripts/export-spec.sh scripts/export-program.sh \
  scripts/check-mirror.py scripts/gen-keywords.sh scripts/time-elab.sh \
  test/diff/run.py .github/workflows/ci.yml
do
  if [ ! -e "$root/$path" ]; then say "missing: $path"; fail=1; fi
done

if find "$root" -path "$root/upstream" -prune -o \( -name 'CLAUDE.md' -o -name 'CLAUDE.local.md' \) -print \
   | grep -q .; then
  say "CLAUDE.md found; instructions live in AGENTS.md alone"; fail=1
fi

link='\]([^)]*\.agents/'
if grep -rnE "$link" "$root/docs" >/dev/null 2>&1; then
  say "docs/ links into .agents/:"; grep -rnE "$link" "$root/docs"; fail=1
fi

"$root/scripts/check-text.sh" || fail=1
"$root/scripts/check-imports.sh" P4SpecTec P4SpecTecTest P4Lib NanoP4Spec P4Spec || fail=1
python3 "$root/scripts/check-mirror.py" || { say "mirror check failed"; fail=1; }

if command -v lake >/dev/null 2>&1; then
  (cd "$root" && lake build --wfail) || { say "lake build --wfail failed"; fail=1; }
  (cd "$root" && lake test) || { say "lake test failed"; fail=1; }
  "$root/scripts/gen-keywords.sh" --check || { say "keyword table is stale"; fail=1; }
  (cd "$root" && lake exe p4spectec-gen exports/nano-p4.al.json --lib NanoP4Spec --check) \
    || { say "NanoP4Spec/ is stale; run: lake exe p4spectec-gen exports/nano-p4.al.json --lib NanoP4Spec --update"; fail=1; }
  (cd "$root" && python3 test/diff/run.py) || { say "differential test failed"; fail=1; }
elif [ "${P4SPECTEC_SKIP_LEAN:-0}" = "1" ]; then
  say "lake not on PATH; Lean gate SKIPPED by P4SPECTEC_SKIP_LEAN=1 (not a pass)"
else
  say "lake not on PATH; install elan or set P4SPECTEC_SKIP_LEAN=1 to skip explicitly"; fail=1
fi

if [ "$fail" -ne 0 ]; then say "FAILED"; exit 1; fi
say "all checks passed"
