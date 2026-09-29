# Proof build performance

Active, 2026-09-28. A user-authorized, time-boxed pass (five hours) at certificate
build latency on branch `n3-perf`, cut from the WIP `n3-core` head `57928eb`. Retained
for its measurements, review and the open follow-ups below. Public results are not written yet: `docs/performance/` gets a snapshot once
the gate passes.
No generated statement, axiom set or certificate obligation changed; only tactic
internals, the placement of generated `#audit_axioms` commands and the reuse of
simplification work.

## Findings

Measured with `lake env lean -Dprofiler=true -Drefine_al.trace=true` on the heaviest
certificate, `Refinement/bin_op.lean` (540s in the last full build):

- Kernel checking is about 10s of it; elaboration is `simp` inside `refine_al` and
  `realize_al` normalization.
- `refines` made 1,887 goal normalizations and 21,449 hypothesis normalizations. About
  12,000 of the latter made no progress, most on unchanged inputs, and each formatted its
  failure message (25s in all) only to decide whether to trace it.
- `real` equalled `user` time: the module's two proofs ran one after the other. Three
  causes, each found by timing probes and `sample` stacks: `Environment.constants`
  scans (forcing the kernel environment), each `#audit_axioms` directly after its
  theorem, and simp-set elaboration by name inside `namespace NanoP4Spec`. Resolving
  `P4SpecTec.….match_rule.eq_1` there tests prefixed and private candidates against
  the reserved-name predicates, and the matcher predicate reads a synchronous
  environment extension, which waits for every pending proof.
- The certificate import chain `bin_eq → bin_op → Expr_eval → Call_eval → …` is the
  critical path. With 16 cores, total CPU is not the limit.

## Changes

- `Tactic/Refine/Normalize.lean`: failure messages are formatted only when tracing. A
  per-invocation memo records normalizations that made no progress, keyed by the
  statement, the rewriting facts and the hypotheses the default discharger may assume.
  `seededSimp` reuses closed results (term, normal form and proof closed, constants
  imported) between normalizations, partitioned by `closedInputs`. `prepareSimpSet`
  builds the rule set from constant names, as `simp` adds a constant argument.
- `Tactic/Constants.lean`: non-blocking listing of a prefix's constants, replacing the
  `env.constants` scans in `ForwardRules.lean` and `Encoding.lean`.
- `Tactic/Refine/ForwardRules.lean`: the fixed interpreter rules' equation, unfolding
  and matcher lemmas are realized once in the library.
- `Codegen/Emit.lean`: `hoistAudits` moves generated audits to the end of their
  namespace or section, ahead of any `mutual` block; `NanoP4Spec/` regenerated.

## Measurements

Local, Apple M3 Max (16 CPUs), Lean 4.34.1, all dependencies warm, full rebuild of
every certificate after a tactic change (`lake test`):

| Measure | Before | After |
|---|---:|---:|
| `lake test` wall time | not completed (see below) | 11m34s (`after3`, pre-review code) |
| Certificate critical path (import graph × module times) | 20.5 min (previous-session log) | 10.9 min |
| Sum of module times | 95.5 min | 57.5 min |
| `Refinement/bin_op` | 540s | 173s |
| `bin_eq` / `Expr_eval` / `Call_eval` / `Decl_load` | 176 / 120 / 222 / 204s | 132 / 79 / 148 / 101s |

`bin_op` in isolation: 625s (profiled, serial) → 164s wall / 287s CPU. The same-machine
baseline run in a separate worktree at `57928eb` was not usable: it spent 6,040s in
`Expr_ok` and was stopped. The previous-session log gives 473s for that module, so
the baseline was probably disturbed by concurrent load or machine sleep. Before
numbers therefore come from the previous session's logs (`.artifacts/test{1,3}.log`)
and are not a controlled comparison.

## Rejected or open

- Carrying the whole goal memo table between goal normalizations with equal facts:
  only 362 of 1,887 goals could reuse it (a changed context blocks the rest), and it
  saved nothing measurable. Removed.
- Unpartitioned closed-result reuse broke eight certificates (`realize_al` step limit).
  A fact with a closed rule side (`rf_c_encoding`) could no longer rewrite cached
  closed terms. Fixed by `closedInputs`; kept as a pitfall.
- Open: goal normalization is still about half of `refine_al`. Each step re-simplifies
  the whole goal, including unchanged open subterms. `expose.obtain` is next (~8%).
  Splitting `refines` and `realizes` into separate modules would let each chain wait
  only on its own kind of callee theorem.
- Open: the pre-existing `P4SpecTecTest/Codegen/Certificates/Producer.lean:76` guard
  expects a two-output relation to be rejected. `57928eb` intentionally made such
  relations supported, so the full gate fails there independently of this work (N3
  resume step 1).

## Review

Independent read-only review (Claude Opus subagent, working tree before the
review fixes). Findings and resolutions:

1. Closed results ignored local facts (medium). Confirmed by the build: eight
   certificates failed. Fixed with `closedInputs`, verified on six of them.
2. Caches survive backtracking but realized constants do not. Harvesting is now
   limited to results whose constants are imported.
3. The no-progress key missed discharger assumptions. Now in the key.
4. and 5. A line over 100 characters and history-style comments. Fixed.
6. A simproc name among the lemmas would be unfolded. Now added as a simproc.
8. Duplicate imported constants. Deduplicated.
9. Pre-realization misses the matchers of unfolding equations. Performance only; open.
10. `hoistAudits` flushed audits into a `mutual` block (found by the build first).
    Fixed.

## Gate (2026-09-28, final working tree)

`nix develop -c scripts/check.sh` exited 1. "Library and certificate build" passed, so
every certificate builds and audits clean. Failing stages:

- Caused by this work: "Certificate replay contracts"
  (`test_generated_modules_keep_what_kept_theorems_use`: `replay-cert.py` expects each
  audit next to its theorem) and "Field-update mutation runner contracts" (its anchor
  `(ExceptT.mk (NanoP4Spec.«$update_fieldValue» p0 p1 p2))` must occur once). Both
  scripts need updating for hoisted audits. Later stages ("Completion inventory,
  coverage and quotation", "Field-update certificate mutations") were not yet
  diagnosed.
- Present at `57928eb` already: 20 long lines in generated `Equality.lean` and four in
  `Codegen`/`Forward.lean`, runtime `CallAdmission` modules unreachable from the
  library root, and the stale `Producer.lean:76` guard.

## Autonomous stabilization and optimization (2026-09-28)

User-authorized continuation: first restore the full gate and CI, then optimize the
remaining N3 workflows with measured results. Published WIP history is retained.
N3 completion itself is not claimed by a green intermediate checkpoint.

Fresh baseline on the existing `694e616` tactic artifacts, with no concurrent Lean
build: `nix develop -c /usr/bin/time -p lake env lean
NanoP4Spec/Refinement/bin_op.lean` exited 0; wall 173.77s, user 302.03s, system 2.27s.
Raw evidence: `.artifacts/perf/codex-baseline-bin-op.log` (ignored).

Independent read-only review by Codex GPT-6 Astra of `694e616`/`deaa47a` found:

- Across 682 changed generated modules, all 3,894 audits and all nonblank,
  non-audit lines were preserved by audit hoisting.
- No kernel-soundness escape identified. Runtime-domain and extern assumptions
  remain explicit; the four missing polymorphic domains remain mandatory.
- Two tactic-completeness fixes required: simplification cache keys must include
  reducible aliases of discharger assumptions, and imported constant inventories
  must not use a process-global prefix-only cache across different environments.
- Stabilization review found that generated cleanup must reject or skip a symlink
  at the library root as well as symlinked children. Regression coverage required.

Resolution: both cache findings are fixed with conservative keys and environment-local
constant enumeration. Generated cleanup rejects a symlinked library root, skips linked
children, and preserves handwritten/foreign-generator files. Regression tests cover
each boundary. Codex GPT-6 Astra re-reviewed the implementation with no remaining
blocking finding; the final two-environment regression exercises `importedUnder` itself.
The review was read-only and did not execute builds; it prioritized the performance
changes and contract boundaries, not an exhaustive re-review of every N3 tactic.

Read-only planning investigation by Codex GPT-6 Sol identified a direct remaining-N3
bottleneck: `SourceBuiltin.field` invokes recursive representation planning instead
of using `Emit.plan`'s existing catalog. Polymorphic source-domain generation also
repeats planning separately for declarations, type and dependencies. Reuse that
catalog before extending the four missing domain proof shapes.

The full stabilization gate `nix develop -c /usr/bin/time -p scripts/check.sh` exited
0: wall 1073.97s, user 4271.05s, system 441.99s; certificate/library build 903s.
No stages were skipped. `.artifacts/perf/codex-stabilization-gate.log` retains the
actual result. Focused replay/mutation Python contracts, generator cleanup tests,
and `lake build P4SpecTecTest.Tactic.Refine` also exited 0. The gate checks the
regenerated tree and refreshed completion manifest, with N3 still incomplete.

Rebuild module times include `bin_eq` 159s, `bin_op` 316s and `Expr_ok` 399s. They are
not directly comparable to the earlier isolated `bin_op` baseline. A one-second
sample of `bin_op` found the active worker in proof finalization: 60/89 samples in
`shareCommonPreDefs`, 21/89 in `partitionPreDefs` constant traversal. The audit was
waiting for that proof. This identifies a candidate bottleneck, not its total share
of the run. Measure exact structural sharing after simplification before changing
the normalization algorithm; no stale normal form may hide a newly applicable rule.
