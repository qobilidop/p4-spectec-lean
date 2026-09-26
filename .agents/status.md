# Status

Current state only; git history is the archive. Updated 2026-09-25.

## Goal and authorization

M1 and M2 are closed. M3A is complete and merged. **M3B is active; M3 is
not complete.** The user authorized autonomous staged completion of M3B–M3F,
routine reversible decisions, suitable subagents, independent reviews and
green PRs. Record uncertain decisions for later review. This does not
authorize weakening correctness or rewriting published history. Phase plan
and exit criteria: `.agents/notes/full-p4-reconnaissance.md`.

## Active frozen checkpoint: bounded corpus shard

PR #22 merged as `2c85f1b` after remote Gate `36213412457` passed on
`93a2e8c` in 3m43s. The new `m3c-corpus-shards` branch starts at that main
revision in the corpus worktree, preserving the published checkpoint ref.
Root approved the strict-identity/crash-safe shard design and exactly shard
0 of 317. Independent root review found no remaining findings after the
quarantine order/worker exit and separately reviewed compiler hardlink fixes;
worker/v1 semantics remain unchanged. Sixteen new offline tests and existing
5+7+12 tests pass; text and whitespace checks exit 0. Final-helper fresh
pilot exit 0, run `901d53d9`:
four attempts/eight AL matches/eight CLI checks, all Type.Fresh phases zero,
no syntax-only/resource/unsupported/harness failures. Exact resume exit 0:
same identity/probe bytes, no new session lines, all attempts remain one,
and all four terminal-record hashes are unchanged. Narrow independently
reviewed CI wiring requires both new files and runs sixteen offline tests
unconditionally, with no real shard/network in CI. Authorized full local
gate process exited 0 without skips, including both 78-program Nano legs,
48 output contexts, 342 quotations, existing oracles/census and new offline
suite. Log: `.artifacts/corpus-shard-full-gate.log`. No scale-up or push;
root authorized one scoped local checkpoint commit next.
Evidence, bounds and commands: `.agents/notes/full-p4-corpus-shards.md`.
Next: inspect/stage the reviewed checkpoint and commit with fresh attribution;
no larger launch before independent review and explicit staged approval.

## Merged checkpoint: corpus inventory and bounded worker

Branch `m3c-corpus-replay` is based on main `e31c1e8` after PR #21 merged.
PR #21's final remote Gate `36210406850` passed on `fed4187` in 5m36s.
The root approved staged inventory, versioned type-fresh sentinel and
spec-once worker implementation, preserving the published v1 APIs; no
gate edits or corpus scale-up before focused independent review.
Read-only Type.Fresh census/six dynamic checks and a synthetic escaping-name
sequence are recorded in `.agents/notes/type-fresh-reachability.md`; no
formal reachability or whole-corpus claim. Plan:
`.agents/notes/full-p4-corpus-replay-plan.md`.

First inventory execution exposed a raw/canonical denominator distinction:
1,352 raw sample paths include eighteen helpers beneath `include`, which
upstream's collector skips. Canonical collection is 1,334 paths with 67
static exclusions and 1,267 candidates; the 68 positive references include
one stale path. The initial offline raw-count expectation failed, preserving
this observation before replay. Root independently inspected the pinned
collector and eighteen helper identities, approving complete manifest
accounting and the corrected canonical denominator. The regenerated 273,394
byte manifest retains all identities/source digests/symlinks and static
exclusion provenance. Five offline tests pass, including thirteen corruption
mutations, literal comment/EOF parsing, helper skip and shard partitioning;
the real exact-pin `inventory.py --check`, text and diff-whitespace checks
exit 0. Root independently reviewed/reran the inventory checks with no
findings; `.agents/reviews/m3c-corpus-inventory.md`.

Follow-up v2 probe/spec-once worker and bounded original-fixture pilot are
independently reviewed with no remaining blocking finding. Root reran seven
offline tests and the pinned pilot (exit 0, report `98530`); review:
`.agents/reviews/m3c-corpus-worker.md`. Published v1 files are unchanged. The
84-job worker build, seven v2 offline tests, text/import/file-size/diff checks and final
fresh pinned pilot exited 0: six AL matches, one explicitly syntax-only case,
eight CLI parity checks and sixteen actual Lean mutations. All original
Type.Fresh phases are zero; any nonzero phase is explicitly unsupported.
Resource bounds/phase timings and exact commands are recorded in
`.agents/notes/full-p4-corpus-worker.md`. Largest case is 30,858,825 bytes;
child RSS high-water is cumulative, not per-case. No corpus shard, resume
implementation or whole-corpus claim. Authorized
narrow gate wiring requires nine paths, runs both offline suites and builds
the worker, with no p4c fetch or upstream-dependent real pilot in CI. Independent
wiring review found no issues and reran shell syntax plus both offline suites
(exit 0); `.agents/reviews/m3c-corpus-gate.md`. Frozen
`nix develop --command bash scripts/check.sh` process exited 0 with no skips,
including both Nano differential legs, existing oracles/census and new
offline suites/worker build. Actual exit was captured before preparing a
push. Final remote Gate passed and PR #22 merged as recorded above.
Shard/resume implementation is a separate next checkpoint.

## Merged checkpoint: checked type runtime

Branch `m3c-type-runtime` adds bounded checked Expand/Equiv/Subst, matcher
and signature conversion APIs and wires the interpreter to explicit hard
errors/divergence instead of type false/identity fallbacks. Legacy pure
APIs remain for proof compatibility. Nonempty FuncT substitution is
explicitly unsupported until separate Type.Fresh state is modeled; no
observable fresh names are invented. See `.agents/notes/type-runtime.md`
and the named deviations in the design. `lake build --wfail P4SpecTec
P4SpecTecTest` passed after the checked signature wiring (153 jobs,
including existing Nano refinement modules). The upstream Nix-shell
`test/type-runtime/run.py --upstream <primary pinned checkout> --check`
passed all fourteen observations; three offline provenance tests and
check-text/check-imports passed. Initial broad build failed only because
the fresh worktree lacked the ignored Nano JSON; verified snapshot
extraction fixed that prerequisite. Full gate, corpus replay and
publication are not claimed. Root independently reviewed all changed paths
and reran TypeRuntime, fourteen pinned cases and three offline tests (all
exit 0); no findings remain within the bounded claim. Review:
`.agents/reviews/m3c-type-runtime.md`. Offline CI wiring was independently
reviewed with no findings; it requires seven paths and unconditionally runs
three offline tests, without real upstream execution/network. Root's shell
syntax check passed. PR 18 is merged into this branch. Frozen
`nix develop --command bash scripts/check.sh` exited 0 with no skips,
including both 78-case Nano differential legs, 48 exact output contexts,
342 quotations, existing printer/text/state oracles, census and new offline
contracts. Actual process exit was recorded before preparing a push.
Published as PR #21 at `268ac98`; its initial remote Gate `36209329791`
passed in 15m55s.
After PR #20 merged as `e0d1bce`, main was reconciled into this branch:
the checked type-runtime source/tests merged unchanged, and overlapping
decision and gate additions retain both reviewed slices. Independent
reconciliation review found no issues and reran the three type-runtime,
six replay and twelve oracle offline tests plus shell syntax (all exit 0):
`.agents/reviews/m3c-type-runtime-reconcile.md`. The frozen reconciled
`nix develop --command bash scripts/check.sh` process exited 0 with no skips,
including both Nano legs and the incoming replay build. Final merged-head
remote Gate `36210406850` passed in 5m36s on `fed4187`; PR #21 merged
as `e31c1e8`. No whole-corpus/type-fresh claim.

## Active checkpoint: generator integration

Bounded refinement PR branch `m3c-state-refinement-pr`, based on merged main
`b08ab8e`, integrates reviewed implementation `de73566`: new
`Codegen.StateValidate` and `state_refine_al` emit and prove
exact all-outcome state contracts for first-order scalar functions and the
actual fresh builtin. Actual-emission fixtures cover fresh dispatch, consumed
rejected prefixes, boolean selection, nested function calls, scalar aliases,
debug allocation, final mismatch, and a hard error that prevents fallback.
The pinned `lake build --wfail P4SpecTec P4SpecTecTest.StateValidate` exited 0
(78 jobs; final fixture elaboration 37 seconds); import completeness, text,
and diff-whitespace checks exited 0. Root independently read the complete
implementation and directly re-elaborated the emitted fixture (exit 0), with
no correctness findings; `.agents/reviews/m3c-state-refinement.md` records
the review and the required production dependency/exclusion handling.
The full pinned `scripts/check.sh` on this PR branch exited 0 with no skips,
including both Nano differential legs, quotation/oracle checks and the full-P4
census. PR #19's initial remote Gate passed on `c54e4eb` (run `36207315308`,
5m25s). After PR #18 merged as `ea9533d`, its oracle source/gate changes
merged cleanly here; only this status document conflicted. The bounded
refinement source remains byte-identical to `c54e4eb`. Root independently
reviewed the status resolution; its two documentation corrections are fixed.
The merged source's frozen full `scripts/check.sh` exited 0 with no skips,
including all twelve oracle contract tests and both Nano differential legs.
Final remote Gate `36209122762` passed on `05769b8` in 3m40s, including
both branch-pin checks; PR #19 merged as `c974c3d`.
Production Emit integration is explicitly out of this PR. See
`.agents/notes/state-refinement.md`.

Isolated state-proof checkpoint on `m3b-state-props`: ordered and optional
structural iteration now emits auxiliary predicates with explicit captured
indices and proves successful runs using ordered chains. Nested, joint,
shadowed and pattern-bound captures are exercised by actual-emission tests.
The build `lake build --wfail P4SpecTec P4SpecTecTest.StateProps` in the pinned
Nix shell exited 0 (72 jobs), as did text and diff-whitespace checks.
The isolated checkpoint's focused results were independently rechecked
in the integration below; they did not alone authorize a push. See
`.agents/notes/state-props.md`. Next: independent review, then recursive SCC
all-outcome realization and structural soundness; production remains disabled.

The executable checkpoint `e0d7219` and structural proof checkpoints
`381dd6a`, `25ad4f2`, `815b671` are integrated on
`m3b-generator-integration`. The reproduced review findings are fixed.
Root independently checked the integrated 78-job focused build and direct
StateProps re-elaboration (both exit 0); reviews are
`.agents/reviews/m3b-state-codegen-followup.md` and
`.agents/reviews/m3b-state-iteration.md`. Production stateful generation
remains guarded until recursive run-soundness is integrated. The refreshed
census reports zero executable emission failures and 256 explicit pure-Prop
rejections, with no generated stateful refinement candidates. This records
text emission, not full-P4 elaboration. The integrated full
`scripts/check.sh` exited 0 with no skips, including both Nano differential
legs, all existing oracles and the refreshed census. Final remote CI passed.

PR #16 passed remote Gate and merged as `87e9181`: actual fresh dispatch
now has an all-fuel exact-state refinement boundary, with explicit disabled
guards and declaration lookup hypotheses. Its full local gate and independent
review passed. That checkpoint is now merged into this integration branch;
the combined revision, including the actual-emitted allocator refinement
fixture, passed a fresh full `scripts/check.sh` (exit 0, no skips).
The fixture independently passed a 75-job build and direct Lean elaboration;
review: `.agents/reviews/m3b-emitted-fresh-refinement.md`. PR #17's final
remote Gate passed in 12m11s (run `36205479916`), and it merged as `b08ab8e`.
Recursive proof integration and production enablement continue separately.

## Merged checkpoint: bounded full-P4 interpreter replay

The separately reviewed replay revisions `a4c907b` and `5657373` are being
integrated on `m3c-p4-replay-publish`, based on merged main `ea9533d`.
Source and tests are unchanged from independent review.
Root reran six offline tests and the pinned end-to-end driver: six relation
matches, one explicitly syntax-only case and nine Lean-side mutation
rejections (exit 0 each). The ordinary gate now requires the replay files,
runs its six offline contract tests and builds the Lean runner; it does not
fetch p4c or run the upstream-dependent real replay. The integrated full
`scripts/check.sh` exited 0 with no skips; independent gate-plumbing review
also passed, including six offline tests and shell syntax (exit 0 each).
PR #20's initial remote Gate `36209104840` passed on `94fd99e` in 4m53s.
Main `c974c3d` merged without source conflicts; only this status document
needed reconciliation. Replay implementation/tests remain byte-identical
to `94fd99e`. The repeated frozen full local `scripts/check.sh` exited 0
with no skips, including twelve oracle and six replay offline tests. Final
remote Gate `36209771264` passed on `0036247` in 4m44s, and PR #20
merged as `e0d1bce`. Root independently reviewed the
status resolution with no findings. Reviews:
`.agents/reviews/m3c-p4-interpreter-replay.md` and
`.agents/reviews/m3c-replay-gate.md`.

## Merged checkpoint: bounded full-P4 oracle

- Branch `m3c-p4-oracle-publish` integrates reviewed adapter revisions
  `16a2d57` and `997d0ab`. All four initial medium findings are resolved;
  independent AI-agent code and gate-plumbing reviews found no issues.
- The ordinary gate requires six adapter files and runs twelve offline
  contract tests. It does not download p4c, build OCaml or run the real
  full-P4 oracle. Independent focused checks exited 0: twelve offline tests,
  four pinned cases with eight CLI comparisons, and additional in-memory
  sensitivity tests. Exact commands and limits are in
  `.agents/reviews/m3c-p4-oracle-adapter.md` and the corresponding note.
- Published as PR #18 at `093dc4e` after its frozen full gate exited 0
  without skips and its relocated real oracle check exited 0. Remote Gate
  `36205678753` passed in 1m52s. PR #17's merge required a status-only
  conflict resolution against current main `b08ab8e`; source merged cleanly.
  The merged revision's frozen full gate exited 0 with no skips, including
  all twelve offline oracle tests and the updated generator census. Final
  remote Gate `36207757309` passed on `3aa9bab` in 16m27s, including both
  upstream branch-pin checks; PR #18 merged as `ea9533d`.
  The merge body's newline escaping was malformed; attribution
  text is present but not a conventional separate trailer. Published history
  is preserved, and subsequent messages use literal newlines.
- This is an upstream-side oracle only, not Lean replay, a corpus denominator
  or full-P4 generation/refinement evidence.

## Merged checkpoint: pinned corpus preparation

- Branch `m3c-corpus-inputs`, based on reviewed proof head `325db77`.
  Integrates a sparse, exact-pin p4c restore script and ten offline tests.
  Source data stays ignored; ordinary CI requires no p4c network fetch.
  Root independently read the script/tests, verified the restored pin and
  clean status, reran the real idempotence check and all ten offline tests
  (exit 0). Integrated full `scripts/check.sh` exited 0 with no skips,
  including the ten offline restore tests. Published as PR #15; its
  remote Gate passed and it merged as `7d9d356`. Next: the full-P4
  boot/result oracle adapter.
- Pinned input slice in the state-oracle worktree: 1,352 resolved sample
  paths, with 67 matching positive exclusion references. The remainder is
  not an oracle eligibility denominator. One representative sample passed
  upstream typing and instantiation in separate CLI sessions; boot values,
  outputs and counters still need an adapter. No whole-corpus validation.
  Evidence and review: `.agents/notes/full-p4-corpus-prep.md` and
  `.agents/reviews/m3c-corpus-prep.md`.

## Recent recursive proof checkpoint

- Branch `m3b-recursive-state-proofs`, based on effect/oracle head `87e44c7`.
  Integrates recursive-prefix fixture `981cc0b` (review `9c95fba`) and
  ordered structural iteration fixture `2c08752`.
- `RecursivePrefix` proves soundness when a rejected earlier attempt calls
  the same recursive SCC and consumes state. Stronger motives realize every
  terminating outcome. `StateRules` preserves structural positive premises
  through an ordered state chain, not a relation defined as its run graph.
  All theorems have axiom audits.
- Independent direct Lean checks exited 0. Primary focused build
  `lake build --wfail P4SpecTecTest.RecursivePrefix P4SpecTecTest.StateRules`
  exited 0 (44 jobs). Full primary `scripts/check.sh` exited 0 with no skips,
  including both Nano differential legs, quotations, classified oracles,
  transport sensitivity and the full-P4 census. Published as PR #14,
  whose remote Gate passed (20m13s); merged as `39d952a`.
  Reviews: `.agents/reviews/m3b-recursive-prefix.md` and
  `.agents/reviews/m3b-state-rules.md`; corresponding implementation notes
  are under `.agents/notes/`.
- PR #12 (byte integration) and PR #13 (shared interpreter/state oracle)
  passed remote CI and merged. Both final local gates for #13 passed with
  no skips. PR #14 built on #13's head, passed remote CI and merged.

## Parallel work and next steps

- Executable state generator: worktree
  `/Users/qobilidop/my/work/p4-spectec-lean-byte-text`, branch
  `m3b-state-codegen`, base `bf7fb62`. GPT-6 Astra's implementation has had
  independent review: uniform mode, complete attempts, callbacks/externs,
  debug effects, dependency collection and emitted-code tests. Final focused
  StateCodegen/Updates/Text build exited 0 (65 jobs); Nano `--check` exited
  0, all 48 files unchanged. Three reproduced findings are being fixed:
  mixed optional-expression errors, callback-cycle monotonicity, and direct
  function-data validation. Raw builtin/extern callback alias fidelity is
  also being checked before integration. Worktree note:
  `.agents/notes/state-codegen.md`.
- Structural proof generation: worktree
  `/Users/qobilidop/my/work/p4-spectec-lean-state-props`, branch
  `m3b-state-props`. GPT-6 Astra owns `Codegen/StateProps` and run-soundness
  automation, sharing executable AST APIs. Copied executable dependencies
  are not independently owned changes. Capture-free structural chains pass
  Lean positivity; closing over enclosing constructor arguments does not.
  Bounded linear backend `381dd6a` and scope-capture fix `25ad4f2` passed root
  independent review and 63-job builds in the former recursive-prefix tree,
  now branch `m3b-linear-proof-review`. The original failing reviewer probe
  passes unchanged after the fix. Iteration extension remains in progress.
- Root owns production integration. `Emit`, `Props` and `Validate` reject
  stateful production generation until structural rules and proofs are ready.
  Enablement also needs generated state imports and state-aware determinism/
  refinement handling. Never silently omit rung-1 guarantees. Plan:
  `.agents/notes/state-integration.md`.
- M3C preparation is in worktree
  `/Users/qobilidop/my/work/p4-spectec-lean-state-oracle`, branch
  `m3b-state-oracle`, note `.agents/notes/full-p4-corpus-prep.md`.
  The pinned sparse sample/include checkout is restored. The boot/result
  oracle adapter merged as PR #18 after final local and remote gates passed.
  The bounded observations are not the canonical corpus denominator or a
  full-corpus boot claim.
- Follow-up independent review of oracle head `997d0ab` cleared all four
  findings and reran the offline and real four-case checks. An isolated
  interpreter replay branch `m3c-p4-interp-replay` now uses those exact
  typed boot values, semantic outputs and post-boot/final counters. Its
  first run found missing P4 placeholder extern wiring for `issue-212`;
  the bounded config now mirrors the two pinned placeholder constructors.
  Three booted cases and six relation runs match; one syntax-only case is
  explicitly outside Lean AL execution. Six replay contract tests and
  focused Lean build exit 0. A follow-up also rejects nine actual Lean-side
  mutations and uniformly checks syntax mode/guard and signed counter range;
  independent follow-up review and full gate passed before publication.
  Note: `.agents/notes/full-p4-interp-replay.md`.
- Next: checkpoint proof fixtures; independently review and integrate
  executable/proof generators; establish stateful refinement; regenerate
  and elaborate full P4. Then M3C corpus/fidelity, M3D targets (NanoSwitch,
  then v1model/eBPF packet tests), M3E expanded refinement/mutations, M3F
  determinism/usability. Substantial implementation remains.

## Delivered M3B evidence

- Subtype bridges preserve full applications: all 567 full-P4 pairs emit.
  Printing preserves 190 hints and 2,120 case origins; twelve pinned printer
  observations pass. Root-index list/text updates preserve order and bounds.
- ByteText represents semantic text throughout IL/runtime, interpreter,
  generator, printer and existing proofs; names remain Strings. Internal
  operations preserve arbitrary bytes. JSON ingress rejects invalid UTF-8
  and lone surrogate escapes rather than replacing them. Corrupt existing
  expectations fail instead of silently becoming skipped comparisons.
- Text oracle: 46 pinned classified observations (31 success, eleven OCaml
  Failure, four Assert_failure), checked through dispatch, interpreter and
  production-emitted wrappers; four also use actual Nano wrappers. Review
  findings on hard-error classification and JSON replacement are fixed.
- Merged state foundations model signed 63-bit wrap and retain consumed IDs
  on mismatch, hard error and negation. The calculus has all-outcome
  refinement, ordered-map and rejected-prefix rules. Full gates and reviews
  pass; this is not generated stateful refinement.
- PR #13 has one transparent effect-parameterized interpreter, preserving
  the pure API and Nano proofs. Explicit session APIs retain all terminating
  post-states; observation does not rerun calls. Durable upstream oracle:
  ten complete-AL/session cases, five primitive cases, ten corrupt-fixture
  rejections. Primitive mismatch kind and exact state are checked. Upstream
  public AL outcomes collapse internal failure kinds; the fixture documents
  that limit and explicitly disables cache/determinism/guard checks.
  Independent reviews and final full local gates passed without skips.
  Reversing negation fails two distinguishing assertions.
- Latest census: one callable emission failure (`fresh_typeId`), zero
  relation Prop-emission failures, all 567 bridges. Independent emission
  is not full-P4 elaboration or semantic coverage.

## Stable baseline and storage policy

- Nano: 161 types, 76 functions, 77 relations, 48 modules (about 57k lines),
  98 run-soundness theorems (77 individual, 21 group), 65 partial fixpoints,
  18 refinement and two determinism theorems, with axiom audits. Refinement
  covers 18 of 153 callables (18 functions, no relations).
- Both differential legs agree on 78 verdicts (48 pass, 30 fail) and all
  48 successful output contexts. Corpus: 32 positive, 21 negative, 25
  exercises. All 342 generated quotations match their exports.
- Full-P4 AL: 1,689 definitions, 98,387,720 raw bytes, 108 source files,
  80 top-level AL region files. Committed gzip: 2,738,237 bytes; Nano gzip:
  244,303 bytes. Raw spec JSON is ignored/checksum-verified; full-P4 raw
  JSON was never committed. Tracked/indexed files must be below 5 MiB;
  also measure aggregate growth. Do not duplicate pinned source corpora.
- Preserve the expected four patched upstream OCaml files. Use pinned Nix
  shells and separate worktree caches. Freeze scripts/source during a full
  gate; record its exit status before push. Logs/scratch are never committed.

## Remaining fidelity and proof obligations

- Generated stateful structural rules, proof automation and all-outcome AL
  refinement are not delivered. Iteration needs structural witnesses;
  recursive failure equations need transport from approximants to final
  calls. Success-only motives do not suffice.
- Guarded higher-order interpretation: `Match.sub_` rejects FuncT
  (Type.Equiv not ported); type-parameter freshening uses deterministic
  names; raw builtin aliases dispatch by local identifier. Guard-disabled
  fixtures do not establish guarded full-P4 fidelity. Function-valued data
  and rank-polymorphic callback signatures, including hidden aliases, must
  remain explicit rejections until supported.
- Match/check return false and type substitution the identity at fuel zero
  (currently constant 1000); resolve before cast refinement. Audit non-text
  builtin hard exceptions. Observed integer parsing is not completeness.
- Hinted-print refinement needs a stronger contract than note-erasing Rel.
  Shared subtype cases require equal substituted payloads; unsupported
  conversions must not be accepted silently.
- Sliced/nested updates remain unsupported. ExternV ordering uses key-sorted
  compressed JSON rather than structural Yojson order. Constructor naming's
  underscore join and suffix are not fully invertible.
- General codegen mutation tests remain owed; narrow negation/oracle
  sensitivity does not substitute. Target instances and the packet leg
  remain undone. Completeness direction is not claimed.
- Historical Nano refinement timings: 19–89 seconds per group. Monitor
  full-P4 scaling; old timings are not a fresh benchmark. Readability remains
  parked in `.agents/roadmap.md`.

## Blocked

No external blocker requiring user input. Corpus inputs are restored;
generator proof work and the full-P4 oracle adapter remain ongoing work.
