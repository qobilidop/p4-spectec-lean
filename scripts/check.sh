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
# 7. Rung 2: the generated typing relation and the Lean port of the AL
#    interpreter agree with upstream's verdict on every exported Nano-P4
#    program (test/diff/run.py, both legs).
# 8. Quoted Nano-P4 AL matches the decoded export, except regions/hints/VarD.
# 9. The full P4 export decodes and its reconnaissance report is current.
# 10. The bounded field-update certificate's mutations fail at the intended boundaries.
# A missing lake is a failure, not a skip, unless P4SPECTEC_SKIP_LEAN=1 says
# so explicitly.
set -euo pipefail
root="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
fail=0

say() { printf '[check] %s\n' "$*"; }

for path in \
  AGENTS.md README.md LICENSE docs/design.md docs/lean-pitfalls.md \
  .agents/status.md .agents/decisions.md .agents/roadmap.md \
  lakefile.toml lake-manifest.json lean-toolchain \
  P4SpecTec.lean P4SpecTecTest.lean P4Lib.lean NanoP4Spec.lean P4Spec.lean NanoP4Proofs.lean \
  P4SpecTec/Codegen/Main.lean P4SpecTec/Codegen/Keywords.lean \
  P4SpecTec/Refine/Init.lean NanoP4Proofs/FieldUpdate/Certificate.lean \
  NanoP4Proofs/FieldUpdate/test/run.py NanoP4Proofs/FieldUpdate/test/test_runner.py \
  upstream/p4-spectec/README.md upstream/nano-p4-spec/README.md \
  upstream/patches/0001-json-export.patch \
  exports/nano-p4.al.json.gz exports/nano-p4.al.json.sha256 \
  exports/p4.al.json.gz exports/p4.al.json.sha256 \
  exports/programs/nano-p4 scripts/spec-snapshot.py test/snapshot/test_snapshot.py \
  scripts/check-file-sizes.py test/snapshot/test_file_sizes.py test/diff/test_json_boundary.py \
  .agents/notes/p4-census.json P4SpecTecTest/Quote/Main.lean P4SpecTecTest/Census/Main.lean \
  test/print/observed.json test/print/run.py test/print/probe.ml \
  P4SpecTecTest/Print/Main.lean P4SpecTecTest/Text/Main.lean \
  test/text/observed.json test/text/run.py test/text/probe.ml \
  P4SpecTecTest/StateOracle/Main.lean \
  test/state/observed.json test/state/run.py test/state/probe.ml test/state/README.md \
  test/state/test_oracle.py \
  scripts/build-upstream.sh scripts/export-spec.sh scripts/export-program.sh \
  scripts/fetch-p4c.sh scripts/test-fetch-p4c.py \
  scripts/export-p4-oracle.py test/p4-oracle/probe.ml test/p4-oracle/check.py \
  test/p4-oracle/observed.json test/p4-oracle/invalid.p4 test/p4-oracle/test_contract.py \
  P4SpecTec/Runtime/Type/Expand.lean P4SpecTec/Runtime/Type/Equiv.lean \
  P4SpecTecTest/TypeRuntime.lean test/type-runtime/observed.json \
  test/type-runtime/probe.ml test/type-runtime/run.py test/type-runtime/test_contract.py \
  test/p4-oracle/replay.py test/p4-oracle/test_replay_contract.py \
  P4SpecTecTest/Diff/P4Interp/Main.lean \
  P4SpecTec/BackendSim/Core/Object.lean P4SpecTec/BackendSim/NanoSwitch/Pipe.lean \
  P4SpecTecTest/NanoTarget.lean P4SpecTecTest/NanoTargetOracle/Main.lean \
  P4SpecTecTest/NanoPacket/Main.lean test/nano-target/requests.json \
  P4SpecTec/Runtime/Sim/Io.lean P4SpecTecTest/NanoDriver/Main.lean \
  test/nano-target/driver-probe.ml test/nano-target/driver-requests.json \
  test/nano-target/driver-observed.json \
  test/nano-target/observed.json test/nano-target/probe.ml test/nano-target/run.py \
  test/nano-target/packet-probe.ml test/nano-target/packet-run.py \
  test/nano-target/packet-observed.json.gz test/nano-target/packet-observed.json.sha256 \
  test/nano-target/fixture.py test/nano-target/check.py test/nano-target/test_contract.py \
  P4SpecTec/BackendSim/Core/Func.lean P4SpecTec/BackendSim/SpecImpl/Func.lean \
  P4SpecTec/BackendSim/SpecImpl/Unpack.lean P4SpecTecTest/NanoVerify/Main.lean \
  test/nano-verify/requests.json test/nano-verify/observed.json test/nano-verify/probe.ml \
  test/nano-verify/run.py test/nano-verify/contract.py test/nano-verify/test_contract.py \
  scripts/check-spec-pin.py test/nano-verify/test_spec_guard.py \
  P4SpecTecTest/Diff/P4Corpus/Main.lean test/p4-corpus/README.md \
  test/p4-corpus/inventory.py test/p4-corpus/manifest.json test/p4-corpus/test_inventory.py \
  test/p4-corpus/probe.ml test/p4-corpus/contract.py test/p4-corpus/run.py \
  test/p4-corpus/test_contract.py test/p4-corpus/shard.py test/p4-corpus/test_shard.py \
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
python3 "$root/scripts/check-file-sizes.py" || fail=1
python3 "$root/test/snapshot/test_file_sizes.py" || fail=1
"$root/scripts/check-imports.sh" P4SpecTec P4SpecTecTest P4Lib NanoP4Spec P4Spec NanoP4Proofs || fail=1
python3 "$root/scripts/check-mirror.py" || { say "mirror check failed"; fail=1; }
python3 "$root/test/snapshot/test_snapshot.py" || { say "snapshot tests failed"; fail=1; }
python3 "$root/NanoP4Proofs/FieldUpdate/test/test_runner.py" \
  || { say "field-update mutation runner contract tests failed"; fail=1; }
bash -n "$root/scripts/fetch-p4c.sh" || { say "p4c restore script syntax failed"; fail=1; }
python3 "$root/scripts/test-fetch-p4c.py" || { say "p4c restore tests failed"; fail=1; }
python3 "$root/test/p4-oracle/test_contract.py" \
  || { say "P4 oracle contract tests failed"; fail=1; }
python3 "$root/test/type-runtime/test_contract.py" \
  || { say "type-runtime oracle contract tests failed"; fail=1; }
python3 "$root/test/p4-oracle/test_replay_contract.py" \
  || { say "P4 interpreter replay contract tests failed"; fail=1; }
python3 "$root/test/nano-target/test_contract.py" \
  || { say "Nano packet fixture contract tests failed"; fail=1; }
python3 "$root/test/nano-verify/test_contract.py" \
  || { say "Shared verify fixture contract tests failed"; fail=1; }
python3 "$root/test/nano-verify/test_spec_guard.py" \
  || { say "Exact specification input guard tests failed"; fail=1; }
python3 "$root/test/p4-corpus/test_inventory.py" \
  || { say "P4 corpus inventory tests failed"; fail=1; }
python3 "$root/test/p4-corpus/test_contract.py" \
  || { say "P4 corpus v2 contract tests failed"; fail=1; }
python3 "$root/test/p4-corpus/test_shard.py" \
  || { say "P4 corpus shard/resume contract tests failed"; fail=1; }
for name in nano-p4 p4; do
  python3 "$root/scripts/spec-snapshot.py" unpack "$root/exports/$name.al.json" \
    || { say "$name snapshot verification failed"; exit 1; }
done

if command -v lake >/dev/null 2>&1; then
  (cd "$root" && lake build --wfail) || { say "lake build --wfail failed"; fail=1; }
  (cd "$root" && lake test) || { say "lake test failed"; fail=1; }
  "$root/scripts/gen-keywords.sh" --check || { say "keyword table is stale"; fail=1; }
  (cd "$root" && lake exe p4spectec-gen exports/nano-p4.al.json --lib NanoP4Spec --check) \
    || { say "NanoP4Spec/ is stale; run: lake exe p4spectec-gen exports/nano-p4.al.json --lib NanoP4Spec --update"; fail=1; }
  (cd "$root" && python3 test/diff/run.py) || { say "differential test failed"; fail=1; }
  python3 "$root/test/diff/test_json_boundary.py" \
    || { say "JSON transport/output checks failed"; fail=1; }
  (cd "$root" && lake build --wfail check-quotes check-print check-text-builtins \
    check-state-oracle p4spectec-census p4-interp-replay p4-corpus-worker \
    check-nano-target check-nano-packet check-nano-driver check-nano-verify) \
    || { say "reconnaissance tools failed to build"; fail=1; }
  (cd "$root" && lake exe check-quotes) || { say "quotation check failed"; fail=1; }
  python3 "$root/NanoP4Proofs/FieldUpdate/test/run.py" \
    || { say "field-update certificate sensitivity checks failed"; fail=1; }
  (cd "$root" && lake exe check-print) || { say "print oracle check failed"; fail=1; }
  (cd "$root" && lake exe check-text-builtins) \
    || { say "text builtin oracle check failed"; fail=1; }
  (cd "$root" && lake exe check-state-oracle) \
    || { say "stateful interpreter oracle check failed"; fail=1; }
  python3 "$root/test/state/test_oracle.py" \
    || { say "state oracle sensitivity check failed"; fail=1; }
  python3 "$root/test/nano-target/check.py" \
    || { say "Nano dynamic target and packet relation replay failed"; fail=1; }
  (cd "$root" && lake exe check-nano-verify) \
    || { say "Shared verify and Nano dispatch replay failed"; fail=1; }
  (cd "$root" && lake exe p4spectec-census exports/p4.al.json --check .agents/notes/p4-census.json) \
    || { say "P4 census is stale or the export does not decode"; fail=1; }
elif [ "${P4SPECTEC_SKIP_LEAN:-0}" = "1" ]; then
  say "lake not on PATH; Lean gate SKIPPED by P4SPECTEC_SKIP_LEAN=1 (not a pass)"
else
  say "lake not on PATH; install elan or set P4SPECTEC_SKIP_LEAN=1 to skip explicitly"; fail=1
fi

if [ "$fail" -ne 0 ]; then say "FAILED"; exit 1; fi
say "all checks passed"
