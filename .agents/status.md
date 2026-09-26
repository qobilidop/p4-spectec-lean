# Status

Current state only; git history is the archive. Updated 2026-09-25.

## Goal and authorization

M1 and M2 are closed. M3A is complete and merged. **M3B is active; M3 is
not complete.** The user authorized autonomous staged completion of M3B–M3F,
routine reversible decisions, suitable subagents, independent reviews and
green PRs. Record uncertain decisions for later review. This does not
authorize weakening correctness or rewriting published history. Phase plan
and exit criteria: `.agents/notes/full-p4-reconnaissance.md`.

## Active isolated checkpoint: checked type runtime

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
`.agents/reviews/m3c-type-runtime.md`. Next: offline CI wiring and integration.

## Active checkpoint: generator integration

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
legs, all existing oracles and the refreshed census. Remote CI remains owed.

PR #16 passed remote Gate and merged as `87e9181`: actual fresh dispatch
now has an all-fuel exact-state refinement boundary, with explicit disabled
guards and declaration lookup hypotheses. Its full local gate and independent
review passed. That checkpoint is now merged into this integration branch;
the combined revision, including the actual-emitted allocator refinement
fixture, passed a fresh full `scripts/check.sh` (exit 0, no skips).
The fixture independently passed a 75-job build and direct Lean elaboration;
review: `.agents/reviews/m3b-emitted-fresh-refinement.md`. Published as PR #17;
remote CI must pass on its final revision before merging. Recursive proof
integration and production enablement continue separately.

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
  oracle adapter remains to be implemented. Regression files alone do not
  establish the canonical corpus denominator. No full-corpus boot claim.
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
