# Performance work: retained constraints and review provenance

Durable; compacted 2026-10-06 from `ci-performance.md` (build, test and CI, closed
2026-09-26 at `4cba852`) and `proof-build-performance.md` (N3 proof builds, closed
2026-09-29), both recoverable at `0e4b521:.agents/notes/`. Measurements and reproduction
live in the public snapshots
[build-test-ci-2026-09-26](../../docs/performance/build-test-ci-2026-09-26.md) and
[n3-iteration-2026-09-28](../../docs/performance/n3-iteration-2026-09-28.md); the
guide is [Performance](../../docs/performance.md). Ignored raw artifacts under
`.artifacts/ci-performance/` and `.artifacts/proof-repeat-study/` are not assumed to exist.
Current performance obligations are in [status](../status.md).

## Constraints that still bind

- Measured comparisons use matching machines, cache conditions and parallelism, with
  balanced ABBA runs for native executables; GitHub run durations are observations, not
  controlled benchmarks (workflow elapsed is created-to-updated time). Do not change
  executable inputs during a measured validation: a whitespace edit to `Prelude` during
  one run invalidated traces and produced apparent duplicate certificate work, which is
  not evidence of a Lake or proof duplication bug.
- Profile before optimizing. Native sampling of the census found
  `Funcs.monotonicityConsumers` re-walking every definition (about 83 to 84 s, then 14 to
  15 s after one adjacency construction per invocation) and then `Yojson.validateEscapes`
  materializing the packed buffer at every byte (`bytes[index]?`, about 13 to 14 s, then
  4 to 5 s); both kept byte-identical Nano generation and the committed census. Short
  samples vary: report the range, not a precise factor. Native sampling counts active
  threads, not time.
- `Tactic/Refine/Normalize.lean` cache boundaries are in `docs/lean-pitfalls.md`
  (selected facts, imported constants; both with regressions). One more from review:
  an imported-constant inventory must be per environment (`env.isImportedConst`), never a
  process-global, prefix-only cache shared across environments.
- Shared `Tactic.Refine.Normalize` changes invalidate forward and reverse proofs;
  generator and source-support changes do not invalidate the heavy `bin_op` and
  `Expr_eval` proofs. Lake hashes contents, so regeneration of byte-identical output
  rebuilds nothing. Replay against stale imports is not evidence for new statements:
  build the actual targets.
- The field-update mutation runner runs the complete baseline first, then independent
  mutants on bounded workers with ordered results; a worker failure rejects the run.
  Packet fixture mutations copy only the path they change and revalidate the source
  fixture afterwards.
- Native dependency ownership: launchers declare `needs` for the model and certificate
  artifacts without adding them to their link closure; the refinement tactic objects are
  linked into none of the four Nano executables (decisions, "Nano certificate shape and
  evidence", native bullet). Forward modules omit direct `Realize` imports, although
  shared extern support may reintroduce that dependency. The native loader needs
  Batteries before core (a core-only load crashed).
- Measurement limits to preserve: the 173.77 s isolated replay against the initial
  `694e616` artifacts predates the cache-completeness repairs and is not the comparison
  baseline for the final implementation; the earlier "540 s to 173 s" had different build
  conditions. Early GitHub runs (`5687b0d` 6m15s, `ad1ac33` 22m44s) are observations under
  different cache states.
- A separate review observation, not an import-cleanup regression: empty-spec planning
  appeared to emit a leading cons token; untested, revisit with generator empty-input
  coverage.

## Rejected or discarded experiments

- Exact structural sharing after `simp` (32-result epochs): 293.44 s against 291.29 s
  without it; removed. A one-second stack sample had overemphasized finalization; the
  full profile gave about 5 s to sharing and 3 s to predefinition processing.
- Removing 177 repeated normalization passes that made no progress in the three heavy
  forward proofs: 16.601 to 16.261 s, 10.373 to 9.982 s and 9.039 to 8.705 s, 2 to 4% on
  a bounded pair and within run variation; `Forward` restored byte-for-byte to `4cba852`.
  Revisit only with stronger measurements.
- Whole-core native attachment to the Nano library (decisions, native bullet).

## Review provenance

Codex GPT-6 Sol, GPT-6 Astra and Claude agents authored; every review was AI-agent
review, not human review, read-only and without builds unless stated; each reviewer
excluded its author's files, with diff digests recorded in the original notes.

| Work | Author | Reviewer and outcome | Limit |
|---|---|---|---|
| First checkpoint `2743c3b` (Lake ownership, gate timing) | root | two Sol cross-reviews, no findings | stub traces are author evidence |
| Census graph `859e8aa` | root | Sol `enforce_library_layers`; duplicate-definition fixture added at its request | reviewer ran no build |
| Refinement rule preparation `19195eb` | Astra `review_oracle_refactor` | root, against pinned `mkSimpContext`/`elabSimpArgs`: a trace-location fidelity issue, fixed with a regression, re-reviewed clean | — |
| Stateful rule preparation | Astra | Sol, no issue | — |
| Fixture copying; concurrent mutations | Sol | root; Sol (other agent), no findings | — |
| Packed JSON byte access | root | Astra, no findings | — |
| Native dependency ownership | root | two Sol cross-reviews, addendum after a downstream example lost an indirect import | — |
| Public snapshot; final evidence addendum | root | Sol: two wording findings resolved; no findings | proof timings checked against author evidence, not rerun; workflow elapsed from the integrator's CI metadata; restoration build author evidence |
| Stabilization `694e616`/`deaa47a` (hoisted audits) | Claude | Astra: all 3,894 audits preserved, no soundness escape | not an exhaustive audit of every earlier N3 tactic |
| Fact lookup, cache filtering, catalog reuse, matcher pre-realization, native CLI | Astra (fact lookup by the first reviewer) | a second Astra reviewer, no blocking finding | — |
| Import routes at `4e566fb`; final integration `30467f3`+`ffc21e7` | — | Astra follow-up; executable tree identical to `d28d3b8` | no builds |

Executable validation of the CI work was gate 5946 (exit 0, 44 stages, warm, 51.5 s) and
exact-head CI 36285795982 for `4cba852` (gate 4m02s, different invalidation from earlier
runs). Session ids, intermediate gate figures and binary digests stay in Git only.
