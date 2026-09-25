#!/usr/bin/env bash
# Every gate CI runs. Exit 0 is the only passing verdict.
#
# Today: the repository layout the design names exists, docs/ does not
# link into .agents/, and the Lean packages build when lake is on PATH.
# A missing lake is a failure, not a skip, unless P4SPECTEC_SKIP_LEAN=1
# says so explicitly (the scaffolding checkpoint set it once).
set -euo pipefail
root="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
fail=0

say() { printf '[check] %s\n' "$*"; }

# 1. Layout: every path the design and AGENTS.md rely on.
for path in \
  AGENTS.md README.md LICENSE docs/design.md \
  .agents/status.md .agents/decisions.md .agents/roadmap.md \
  lakefile.toml lean-toolchain \
  P4SpecTec.lean P4SpecTecTest.lean P4Lib.lean NanoP4Spec.lean P4Spec.lean \
  P4SpecTec/Emit/Main.lean \
  upstream/p4-spectec/README.md upstream/patches \
  exports scripts/build-upstream.sh scripts/export-spec.sh scripts/export-program.sh \
  test/diff
do
  if [ ! -e "$root/$path" ]; then say "missing: $path"; fail=1; fi
done

# 2. No CLAUDE.md anywhere: AGENTS.md is the only instruction file.
if find "$root" -name 'CLAUDE.md' -o -name 'CLAUDE.local.md' | grep -q .; then
  say "CLAUDE.md found; instructions live in AGENTS.md alone"; fail=1
fi

# 3. docs/ never links into .agents/ (markdown link targets; prose may name it).
link='\]([^)]*\.agents/'
if grep -rnE "$link" "$root/docs" >/dev/null 2>&1; then
  say "docs/ links into .agents/:"; grep -rnE "$link" "$root/docs"; fail=1
fi

# 4. Lean.
if command -v lake >/dev/null 2>&1; then
  (cd "$root" && lake build) || { say "lake build failed"; fail=1; }
elif [ "${P4SPECTEC_SKIP_LEAN:-0}" = "1" ]; then
  say "lake not on PATH; Lean gate SKIPPED by P4SPECTEC_SKIP_LEAN=1 (not a pass)"
else
  say "lake not on PATH; install elan or set P4SPECTEC_SKIP_LEAN=1 to skip explicitly"; fail=1
fi

if [ "$fail" -ne 0 ]; then say "FAILED"; exit 1; fi
say "all checks passed"
