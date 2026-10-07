#!/usr/bin/env bash
# Every gate CI runs. Exit 0 is the only passing verdict.
#
# 1. Layout the design and AGENTS.md rely on; no CLAUDE.md; docs/ does not
#    link into .agents/.
# 2. Text hygiene (scripts/check-text.sh). Contract tests follow; the ignored extracted
#    exports are removed first and recreated from the committed snapshots, as in CI.
# 3. Module reachability from configured build roots, and one-way imports
#    from consumers through generated models to the reusable core.
# 4. Mirror checks: mirrored modules have upstream's constructors in
#    upstream's order (scripts/check-mirror.py).
# 5. Lean: `lake build --wfail` (warnings fail, and a `sorry` is a warning),
#    then `lake test` and an explicit ExampleProofs build.
# 6. Generated code is current: the keyword table matches the toolchain and
#    the committed NanoP4Spec/ is byte-identical to what the generator
#    writes from exports/nano-p4.al.json.
# 7. Rung 2: the generated typing relation and the Lean port of the AL
#    interpreter agree with upstream's verdict on every exported Nano-P4
#    program (P4SpecTecTest/Oracle/Nano/Replay/replay.py, both legs).
# 8. Quoted Nano-P4 AL matches the export, with typed VarD checked separately.
# 9. The full P4 export decodes and its reconnaissance report is current. Its generated
#    library (ignored sources, regenerated here) matches P4Spec.manifest.json and the
#    committed golden samples, builds with `--wfail`, its quotations match the export, and
#    every theorem its coverage report claims has the claimed type and only allowed axioms.
# 10. The whole-program source-address filter's quotation is current.
# 11. Combined completion (`--require-complete all`): every proof, replay, consumer and
#     sensitivity obligation. It runs check-consumer and the field-update, source-address
#     filter and cross-layer mutation suites; review and release records may be pending.
# A missing lake is a failure, not a skip, unless P4SPECTEC_SKIP_LEAN=1 says
# so explicitly.
set -euo pipefail
root="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
fail=0

say() { printf '[check] %s\n' "$*"; }

# Keep a stage's actual exit status visible without stopping collected-failure checks.
runStage() {
  local label="$1" started=$SECONDS status
  shift
  say "start: $label"
  if "$@"; then status=0; else status=$?; fi
  say "end: $label ($((SECONDS - started))s, exit $status)"
  return "$status"
}

# Lake and the replay runner resolve package-relative inputs from the repository root.
inRoot() (cd "$root" && "$@")

# CI starts without the ignored extracted exports; the snapshot stage below recreates them.
# Remove local copies first so a stage that reads them too early fails here as it does in CI
# (this hid a stage-order bug from local gates twice). Tools run in this checkout while a gate
# is between here and the snapshot stage, or after an interrupted gate, find them absent.
rm -f "$root/exports/nano-p4.al.json" "$root/exports/p4.al.json"

layout_started=$SECONDS
say "start: Repository layout"

for path in \
  AGENTS.md README.md LICENSE docs/design.md docs/lean-pitfalls.md \
  .agents/status.md .agents/decisions.md .agents/roadmap.md \
  lakefile.toml lake-manifest.json lean-toolchain \
  P4SpecTec.lean P4SpecTecTest.lean NanoP4Spec.lean ExampleProofs.lean \
  Tools/Generate.lean P4SpecTec/Codegen/Keywords.lean \
  P4SpecTec/Codegen/Coverage.lean P4SpecTec/Codegen/Coverage/Check.lean \
  NanoP4Spec/coverage.json \
  NanoP4Spec/completion.json scripts/nano-certification.py \
  scripts/test_nano_certification.py P4SpecTecTest/Oracle/Nano/Certification/corpus.py \
  P4SpecTecTest/Oracle/Nano/Certification/corpus.json P4SpecTecTest/Oracle/Nano/Certification/test_corpus.py \
  P4SpecTecTest/Oracle/Nano/Certification/mutations.py \
  P4SpecTecTest/Oracle/Nano/Certification/test_mutations.py \
  P4SpecTec/Refine/Init.lean ExampleProofs/NanoP4FieldUpdate/Certificate.lean \
  ExampleProofs/NanoP4FieldUpdate/test/run.py ExampleProofs/NanoP4FieldUpdate/test/test_runner.py \
  ExampleProofs/NanoP4SrcAddrFilter/Certificate.lean ExampleProofs/NanoP4SrcAddrFilter/Program.lean \
  ExampleProofs/NanoP4SrcAddrFilter/test/run.py ExampleProofs/NanoP4SrcAddrFilter/test/test_runner.py \
  Tools/QuoteProgram.lean Tools/CheckConsumer.lean P4SpecTec/Tactic/LazyEval.lean \
  upstream/p4-spectec/README.md upstream/nano-p4-spec/README.md \
  upstream/patches/0001-json-export.patch \
  exports/nano-p4.al.json.gz exports/nano-p4.al.json.sha256 \
  exports/p4.al.json.gz exports/p4.al.json.sha256 \
  exports/programs/nano-p4 scripts/spec-snapshot.py scripts/test_spec_snapshot.py \
  scripts/check-file-sizes.py scripts/test_file_sizes.py P4SpecTecTest/Oracle/Nano/Replay/test_json_boundary.py \
  scripts/check-text.py scripts/test_check_text.py scripts/test_build_upstream.py \
  scripts/check-library-boundaries.py scripts/test_library_boundaries.py \
  scripts/library-imports.lean \
  .agents/notes/p4-census.json Tools/CheckQuotes.lean Tools/Census.lean \
  P4Spec.manifest.json Tools/CheckP4Quotes.lean \
  scripts/generated-manifest.py scripts/test_generated_manifest.py \
  P4Spec.samples scripts/golden-samples.py scripts/test_golden_samples.py \
  P4SpecTecTest/Oracle/Print/observed.json P4SpecTecTest/Oracle/Print/capture.py P4SpecTecTest/Oracle/Print/probe.ml \
  P4SpecTecTest/Oracle/Print/Main.lean P4SpecTecTest/Oracle/Text/Main.lean \
  P4SpecTecTest/Oracle/Text/observed.json P4SpecTecTest/Oracle/Text/capture.py P4SpecTecTest/Oracle/Text/probe.ml \
  P4SpecTecTest/Oracle/State/Main.lean \
  P4SpecTecTest/Oracle/State/observed.json P4SpecTecTest/Oracle/State/capture.py P4SpecTecTest/Oracle/State/probe.ml P4SpecTecTest/Oracle/State/README.md \
  P4SpecTecTest/Oracle/State/test_oracle.py \
  scripts/build-upstream.sh scripts/export-spec.sh scripts/export-program.sh \
  scripts/fetch-p4c.sh scripts/test_fetch_p4c.py \
  scripts/export-p4-oracle.py P4SpecTecTest/Oracle/P4/Replay/probe.ml P4SpecTecTest/Oracle/P4/Replay/check.py \
  P4SpecTecTest/Oracle/P4/Replay/observed.json P4SpecTecTest/Oracle/P4/Replay/invalid.p4 P4SpecTecTest/Oracle/P4/Replay/test_contract.py \
  P4SpecTec/Runtime/Type/Expand.lean P4SpecTec/Runtime/Type/Equiv.lean \
  P4SpecTecTest/Runtime/Type.lean P4SpecTecTest/Oracle/Type/observed.json \
  P4SpecTecTest/Oracle/Type/probe.ml P4SpecTecTest/Oracle/Type/capture.py P4SpecTecTest/Oracle/Type/test_contract.py \
  P4SpecTecTest/Oracle/P4/Replay/replay.py P4SpecTecTest/Oracle/P4/Replay/test_replay_contract.py \
  P4SpecTecTest/Oracle/P4/Replay/Main.lean P4SpecTecTest/Oracle/P4/Replay/Check.lean \
  P4SpecTecTest/Oracle/P4/Generated/Main.lean P4SpecTecTest/Oracle/P4/Generated/Externs.lean \
  P4SpecTec/BackendSim/Placeholder.lean P4SpecTecTest/BackendSim/Placeholder.lean \
  P4SpecTecTest/Oracle/P4/Corpus/Check.lean P4SpecTecTest/Oracle/P4/Corpus/Generated/Main.lean \
  P4SpecTecTest/Oracle/P4/Corpus/sweep.py P4SpecTecTest/Oracle/P4/Corpus/test_sweep.py \
  P4SpecTecTest/Oracle/P4/Corpus/mutations.py P4SpecTecTest/Oracle/P4/Corpus/test_mutations.py \
  P4SpecTec/BackendSim/Core/Object.lean P4SpecTec/BackendSim/NanoSwitch/Pipe.lean \
  P4SpecTecTest/BackendSim/NanoSwitch/Target.lean P4SpecTecTest/Oracle/NanoSwitch/Target/Main.lean \
  P4SpecTecTest/Oracle/NanoSwitch/Packets/Main.lean P4SpecTecTest/Oracle/NanoSwitch/Target/requests.json \
  P4SpecTec/Runtime/Sim/Io.lean P4SpecTecTest/Oracle/NanoSwitch/Driver/Main.lean \
  P4SpecTecTest/Oracle/NanoSwitch/Driver/probe.ml P4SpecTecTest/Oracle/NanoSwitch/Driver/requests.json \
  P4SpecTecTest/Oracle/NanoSwitch/Driver/observed.json \
  P4SpecTecTest/Oracle/NanoSwitch/Target/observed.json P4SpecTecTest/Oracle/NanoSwitch/Target/probe.ml P4SpecTecTest/Oracle/NanoSwitch/Target/capture.py \
  P4SpecTecTest/Oracle/NanoSwitch/Packets/probe.ml P4SpecTecTest/Oracle/NanoSwitch/Packets/capture.py \
  P4SpecTecTest/Oracle/NanoSwitch/Packets/packet-observed.json.gz P4SpecTecTest/Oracle/NanoSwitch/Packets/packet-observed.json.sha256 \
  P4SpecTecTest/Oracle/NanoSwitch/Packets/fixture.py P4SpecTecTest/Oracle/NanoSwitch/Packets/check.py P4SpecTecTest/Oracle/NanoSwitch/Packets/test_contract.py \
  P4SpecTec/BackendSim/Core/Func.lean P4SpecTec/BackendSim/SpecImpl/Func.lean \
  P4SpecTec/BackendSim/SpecImpl/Unpack.lean P4SpecTecTest/Oracle/NanoSwitch/Verify/Main.lean \
  P4SpecTecTest/Oracle/NanoSwitch/Verify/requests.json P4SpecTecTest/Oracle/NanoSwitch/Verify/observed.json P4SpecTecTest/Oracle/NanoSwitch/Verify/probe.ml \
  P4SpecTecTest/Oracle/NanoSwitch/Verify/capture.py P4SpecTecTest/Oracle/NanoSwitch/Verify/contract.py P4SpecTecTest/Oracle/NanoSwitch/Verify/test_contract.py \
  scripts/check-spec-pin.py scripts/test_spec_pin.py \
  P4SpecTecTest/Oracle/P4/Corpus/Main.lean P4SpecTecTest/Oracle/P4/Corpus/README.md \
  P4SpecTecTest/Oracle/P4/Corpus/inventory.py P4SpecTecTest/Oracle/P4/Corpus/manifest.json P4SpecTecTest/Oracle/P4/Corpus/test_inventory.py \
  P4SpecTecTest/Oracle/P4/Corpus/errors.json \
  P4SpecTecTest/Oracle/P4/Corpus/probe.ml P4SpecTecTest/Oracle/P4/Corpus/contract.py P4SpecTecTest/Oracle/P4/Corpus/campaign.py \
  P4SpecTecTest/Oracle/P4/Corpus/test_contract.py P4SpecTecTest/Oracle/P4/Corpus/shard.py P4SpecTecTest/Oracle/P4/Corpus/test_shard.py \
  scripts/check-mirror.py scripts/gen-keywords.sh scripts/time-elab.sh \
  scripts/replay-cert.py scripts/test_replay_cert.py \
  P4SpecTecTest/Oracle/Nano/Replay/replay.py .github/workflows/ci.yml \
  .claude/skills/tend-repo/SKILL.md
do
  if [ ! -e "$root/$path" ]; then say "missing: $path"; fail=1; fi
done

# Both agents must discover the same skill sources, not independent copies.
if [ ! -L "$root/.claude/skills" ] || [ ! "$root/.claude/skills" -ef "$root/.agents/skills" ]; then
  say ".claude/skills must be a symlink to .agents/skills"; fail=1
fi

if find "$root" -path "$root/upstream" -prune -o \( -name 'CLAUDE.md' -o -name 'CLAUDE.local.md' \) -print \
   | grep -q .; then
  say "CLAUDE.md found; instructions live in AGENTS.md alone"; fail=1
fi

link='\]([^)]*\.agents/'
if grep -rnE "$link" "$root/docs" >/dev/null 2>&1; then
  say "docs/ links into .agents/:"; grep -rnE "$link" "$root/docs"; fail=1
fi

say "end: Repository layout ($((SECONDS - layout_started))s, exit $fail)"

runStage "Text hygiene" "$root/scripts/check-text.sh" || fail=1
runStage "Text checker contracts" python3 "$root/scripts/test_check_text.py" || fail=1
runStage "Upstream build contracts" python3 "$root/scripts/test_build_upstream.py" || fail=1
runStage "Shared oracle build contracts" python3 "$root/scripts/test_oracle_build.py" || fail=1
runStage "Completion inventory contracts" python3 "$root/scripts/test_nano_certification.py" || fail=1
runStage "Nano corpus inventory contracts" python3 "$root/P4SpecTecTest/Oracle/Nano/Certification/test_corpus.py" || fail=1
runStage "Tracked file sizes" python3 "$root/scripts/check-file-sizes.py" || fail=1
runStage "File-size checker contracts" python3 "$root/scripts/test_file_sizes.py" || fail=1
runStage "Generated manifest contracts" python3 "$root/scripts/test_generated_manifest.py" || fail=1
runStage "Golden sample contracts" python3 "$root/scripts/test_golden_samples.py" || fail=1
runStage "Upstream constructor mirrors" python3 "$root/scripts/check-mirror.py" || { say "mirror check failed"; fail=1; }
runStage "Spec snapshot contracts" python3 "$root/scripts/test_spec_snapshot.py" || { say "snapshot tests failed"; fail=1; }
runStage "Certificate replay contracts" python3 "$root/scripts/test_replay_cert.py" || { say "replay tests failed"; fail=1; }
runStage "Field-update mutation runner contracts" python3 "$root/ExampleProofs/NanoP4FieldUpdate/test/test_runner.py" \
  || { say "field-update mutation runner contract tests failed"; fail=1; }
runStage "Source-address filter mutation runner contracts" \
  python3 "$root/ExampleProofs/NanoP4SrcAddrFilter/test/test_runner.py" \
  || { say "source-address filter mutation runner contract tests failed"; fail=1; }
runStage "P4C restore shell syntax" bash -n "$root/scripts/fetch-p4c.sh" || { say "p4c restore script syntax failed"; fail=1; }
runStage "P4C restore contracts" python3 "$root/scripts/test_fetch_p4c.py" || { say "p4c restore tests failed"; fail=1; }
runStage "Full-P4 oracle contracts" python3 "$root/P4SpecTecTest/Oracle/P4/Replay/test_contract.py" \
  || { say "P4 oracle contract tests failed"; fail=1; }
runStage "Type-runtime oracle contracts" python3 "$root/P4SpecTecTest/Oracle/Type/test_contract.py" \
  || { say "type-runtime oracle contract tests failed"; fail=1; }
runStage "Full-P4 replay contracts" python3 "$root/P4SpecTecTest/Oracle/P4/Replay/test_replay_contract.py" \
  || { say "P4 interpreter replay contract tests failed"; fail=1; }
runStage "Nano packet fixture contracts" python3 "$root/P4SpecTecTest/Oracle/NanoSwitch/Packets/test_contract.py" \
  || { say "Nano packet fixture contract tests failed"; fail=1; }
runStage "Shared verify fixture contracts" python3 "$root/P4SpecTecTest/Oracle/NanoSwitch/Verify/test_contract.py" \
  || { say "Shared verify fixture contract tests failed"; fail=1; }
runStage "Exact specification input contracts" python3 "$root/scripts/test_spec_pin.py" \
  || { say "Exact specification input guard tests failed"; fail=1; }
runStage "Full-P4 corpus inventory contracts" python3 "$root/P4SpecTecTest/Oracle/P4/Corpus/test_inventory.py" \
  || { say "P4 corpus inventory tests failed"; fail=1; }
runStage "Full-P4 corpus worker contracts" python3 "$root/P4SpecTecTest/Oracle/P4/Corpus/test_contract.py" \
  || { say "P4 corpus v2 contract tests failed"; fail=1; }
runStage "Full-P4 corpus resume contracts" python3 "$root/P4SpecTecTest/Oracle/P4/Corpus/test_shard.py" \
  || { say "P4 corpus shard/resume contract tests failed"; fail=1; }
runStage "Full-P4 corpus sweep contracts" python3 "$root/P4SpecTecTest/Oracle/P4/Corpus/test_sweep.py" \
  || { say "P4 corpus sweep contract tests failed"; fail=1; }
runStage "Full-P4 sweep mutation contracts" python3 "$root/P4SpecTecTest/Oracle/P4/Corpus/test_mutations.py" \
  || { say "P4 sweep mutation contract tests failed"; fail=1; }
for name in nano-p4 p4; do
  runStage "$name snapshot verification" python3 "$root/scripts/spec-snapshot.py" unpack "$root/exports/$name.al.json" \
    || { say "$name snapshot verification failed"; exit 1; }
done
# The cross-layer runner's contracts read the export extracted above; a warm checkout's copy
# must never be their only input.
runStage "Cross-layer mutation runner contracts" \
  python3 "$root/P4SpecTecTest/Oracle/Nano/Certification/test_mutations.py" \
  || { say "cross-layer mutation runner contract tests failed"; fail=1; }

if command -v lake >/dev/null 2>&1; then
  # The full-P4 library's sources are ignored: regenerate them before anything reads them,
  # and require the digests the manifest records.
  runStage "Generated full-P4 sources" inRoot lake exe p4spectec-gen exports/p4.al.json --lib P4Spec --update \
    || { say "full-P4 generation failed"; fail=1; }
  runStage "Generated full-P4 freshness" python3 "$root/scripts/generated-manifest.py" --check P4Spec "$root/P4Spec.manifest.json" \
    || { say "P4Spec/ differs from P4Spec.manifest.json; if intended: scripts/generated-manifest.py --update P4Spec P4Spec.manifest.json"; fail=1; }
  runStage "Generated full-P4 golden samples" python3 "$root/scripts/golden-samples.py" --check "$root/P4Spec" "$root/P4Spec.samples" \
    || { say "P4Spec.samples/ differs from P4Spec/; if intended: scripts/golden-samples.py --update P4Spec P4Spec.samples"; fail=1; }
  runStage "Library layers and reachability" inRoot lake env python3 "$root/scripts/check-library-boundaries.py" \
    || { say "library boundary check failed"; fail=1; }
  runStage "Library boundary contracts" inRoot lake env python3 "$root/scripts/test_library_boundaries.py" --lean \
    || { say "library boundary regression tests failed"; fail=1; }
  runStage "Library and certificate build" inRoot lake build --wfail || { say "lake build --wfail failed"; fail=1; }
  runStage "Lean unit tests" inRoot lake test || { say "lake test failed"; fail=1; }
  runStage "Downstream example proofs" inRoot lake build --wfail ExampleProofs \
    || { say "ExampleProofs build failed"; fail=1; }
  runStage "Lean keyword freshness" "$root/scripts/gen-keywords.sh" --check || { say "keyword table is stale"; fail=1; }
  runStage "Generated Nano freshness" inRoot lake exe p4spectec-gen exports/nano-p4.al.json --lib NanoP4Spec --runtime-extern value --check \
    || { say "NanoP4Spec/ is stale; run: lake exe p4spectec-gen exports/nano-p4.al.json --lib NanoP4Spec --runtime-extern value --update"; fail=1; }
  runStage "Generated module cleanup contracts" python3 "$root/scripts/test_generate.py" \
    || { say "generated module cleanup contracts failed"; fail=1; }
  runStage "Nano differential replay, both legs" inRoot python3 P4SpecTecTest/Oracle/Nano/Replay/replay.py || { say "differential test failed"; fail=1; }
  runStage "JSON transport contracts" python3 "$root/P4SpecTecTest/Oracle/Nano/Replay/test_json_boundary.py" \
    || { say "JSON transport/output checks failed"; fail=1; }
  runStage "Diagnostic and oracle executable build" inRoot lake build --wfail \
    check-quotes check-coverage check-print check-text-builtins \
    check-state-oracle p4spectec-census p4-interp-replay p4-corpus-worker \
    check-nano-target check-nano-packet check-nano-driver check-nano-verify check-nano-sessions \
    check-target check-consumer nano-program-quote \
    || { say "reconnaissance tools failed to build"; fail=1; }
  runStage "Source-address filter quotation freshness" inRoot lake exe nano-program-quote \
    exports/programs/nano-p4/positive/src-addr-filter.json ExampleProofs.NanoP4SrcAddrFilter \
    ExampleProofs/NanoP4SrcAddrFilter/Program.lean --check \
    || { say "the source-address filter quotation is stale"; fail=1; }
  # Retain bounded N2 closure checks and require combined completion: core and target proofs,
  # both replays, the whole-program consumer and every mutation suite. Review and release are
  # records about one tree digest, written after this gate and CI pass, so they may be pending.
  runStage "Combined completion and mutation suites" python3 "$root/scripts/nano-certification.py" \
    --require-n2 --require-complete all --allow-unpublished \
    || { say "Nano combined completion check failed"; fail=1; }
  runStage "Print oracle replay" inRoot lake exe check-print || { say "print oracle check failed"; fail=1; }
  runStage "Text builtin oracle replay" inRoot lake exe check-text-builtins \
    || { say "text builtin oracle check failed"; fail=1; }
  runStage "State interpreter oracle replay" inRoot lake exe check-state-oracle \
    || { say "stateful interpreter oracle check failed"; fail=1; }
  runStage "State oracle sensitivity" python3 "$root/P4SpecTecTest/Oracle/State/test_oracle.py" \
    || { say "state oracle sensitivity check failed"; fail=1; }
  runStage "Nano target and packet replay" python3 "$root/P4SpecTecTest/Oracle/NanoSwitch/Packets/check.py" \
    || { say "Nano dynamic target and packet relation replay failed"; fail=1; }
  runStage "Nano STF session replay, both paths" python3 "$root/P4SpecTecTest/Oracle/NanoSwitch/Sessions/check.py" \
    || { say "Nano STF session replay failed"; fail=1; }
  runStage "Shared verify and Nano dispatch replay" inRoot lake exe check-nano-verify \
    || { say "Shared verify and Nano dispatch replay failed"; fail=1; }
  runStage "Full-P4 capability census" inRoot lake exe p4spectec-census exports/p4.al.json --check .agents/notes/p4-census.json \
    || { say "P4 census is stale or the export does not decode"; fail=1; }
  runStage "Full-P4 library and tool build" inRoot lake build --wfail P4Spec check-p4-quotes p4-gen-replay \
    p4-corpus-worker-gen \
    || { say "P4Spec build failed"; fail=1; }
  runStage "Full-P4 quotation check" inRoot lake exe check-p4-quotes \
    || { say "full-P4 quotations differ from the export"; fail=1; }
  runStage "Full-P4 coverage claims" inRoot lake exe check-coverage --full-p4 \
    || { say "full-P4 coverage report is stale or a claimed theorem does not check"; fail=1; }
elif [ "${P4SPECTEC_SKIP_LEAN:-0}" = "1" ]; then
  say "lake not on PATH; Lean gate SKIPPED by P4SPECTEC_SKIP_LEAN=1 (not a pass)"
else
  say "lake not on PATH; install elan or set P4SPECTEC_SKIP_LEAN=1 to skip explicitly"; fail=1
fi

if [ "$fail" -ne 0 ]; then say "FAILED"; exit 1; fi
say "all checks passed"
