# Generated certificate coverage

Complete locally, awaiting publication, 2026-09-26. Owns implementation and
review evidence for the approved machine-readable coverage increment.
Broader M3 remains paused.

## Contract and choices

- Reusable schema/checker live in `P4SpecTec.Codegen.Coverage`; output lives
  beside each generated library as `coverage.json`. Nano is the production
  instance today. The full-P4 census stays a distinct capability probe.
- The production planner records claims at its actual emission decisions.
  Human refinement comments and JSON use the same entries. No new fragment
  eligibility algorithm, proof coverage or full-P4 generation is introduced.
- Schema 1 inventories callables, including externs/builtins as boundaries.
  The refinement denominator excludes externs/builtins. Only per-definition
  theorems count; helper group proofs are audited through their dependents.
- Expected theorem types share binder/conclusion construction with emitters.
  The checker requires freshly regenerated metadata, theorem declaration kind,
  definitionally equal types and the existing allowed axiom closure. This is
  metadata consistency checking, not an independent correctness proof of the
  planner or exporter. Source freshness and quotation checks remain separate.
- No cached `checked` field: editing JSON cannot grant a proof. Dependency
  explanations visit direct calls and SCC peers, with shared blocker origins.
- Detailed user-facing contract belongs in `docs/certification.md`, not a
  second report guide. Handwritten consumer certificates remain separate.

## Evidence and review

- Focused Props/Validate warning-failing build passed (28 jobs, agent
  `/root/compact_state`); root Emit/generator build passed (session 45078).
- Root planner fixture tests passed (session 27520). Initial test/API syntax
  errors were fixed before that successful build.
- First Nano regeneration changed only the human refinement index and added
  metadata: all existing emitted theorem and executable sources are unchanged.
  Initial report inventory: 18 refinement, 77 run-soundness, 2 determinism claims.
- Independent read-only `/root/compact_state` review of root Coverage/Emit found
  no new correctness issue. It checked closure bounds, claim emission matching,
  SCC blocker origins and extern/builtin denominator handling. Its own shared
  statement helpers were excluded from that independent review.
- Reviewer noted inherited `detIds` bookkeeping can include recursive relations
  without emitted determinism theorems. A later caller's attempted proof can
  therefore fail compilation. This scope does not widen that fragment; the
  compiled checker must not treat an attempted theorem as checked evidence.

- Compiled Nano checking through normal Lean frontend passed for all 180
  callable entries and 97 claims (root probe session 9607). The standalone
  launcher's raw imported environment lacked notation elaborators; final
  launcher uses pinned `lean --stdin`, escaped arguments and the child exit.
- Final focused checker build and runtime passed (author
  `/root/compact_full_p4`, session 19527): all claims, eleven diagnostic-specific
  mutations and `update_fieldValue` closure. Root's expanded planner fixtures
  pass, including covered SCCs, builtin/extern boundaries and exact stateful
  rejection. Independent structural audit confirms unique IDs and resolved
  dependency/SCC references.
- `/root/compact_full_p4` and root independently reviewed the Props/Validate
  shared-type helpers. Existing emitted theorem sources remain byte-identical.
- Final independent read-only review by `/root/compact_state` found no remaining
  issue in schema/planner, checker, tests, gate wiring, docs or final launcher.
  The reviewer checked argument escaping, pinned executable selection, fresh
  frontend execution and child exit propagation; own statement helpers were
  excluded. Author checks and root full-gate evidence are separate from review.
- Unknown entry-point CLI test propagated exit 1 (author session 29163).

- Full `nix develop --command scripts/check.sh` passed with actual exit 0,
  no skips (session 6398, `.artifacts/coverage-gate.log`). The new runtime checker
  and all existing build, quotation, example sensitivity, differential, oracle
  and census checks passed together. Final documentation/state updates also
  receive text and whitespace checks after that run.

The user explicitly reconfirmed direct commit/push to main, resolving the
conflicting session-supplied PR instruction. Publication follows the completed
local gate and independent review; remote CI remains to be checked for that head.
