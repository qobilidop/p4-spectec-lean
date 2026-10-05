# Status

Active: full-P4 M3, resumed by the user on 2026-10-04 with autonomous authorization
(decisions, "Scope and product"). The Nano-P4 completion milestone stays closed at
`42ffad6` (2026-09-30); [`notes/nano-release.json`](notes/nano-release.json) records its
review and exact-revision CI for that tree digest.

## Where M3 stands

- M3B is closed, pending remote CI for its last commit: the whole full-P4 export generates
  as the library `P4Spec` (ignored sources, pinned by `P4Spec.manifest.json`, sampled in
  `P4Spec.samples/`) with executable definitions, quotations matching the export, a
  state-indexed logical relation for each of the 256 relations, and since 2026-10-05 an
  audited run-soundness theorem for every one of them, the 31 recursion groups included.
  [Full-P4 overview](notes/full-p4/overview.md) has the measurements and what the
  theorems do not say; decisions, "Recursive state run-soundness by fixed-point
  induction", has the method.
- M3C, sweep (`f329af0`): the generated library and the reference interpreter both agree
  with upstream on 1,266 of the 1,267 corpus candidates, for typing and instantiation.
  [Corpus note](notes/full-p4/corpus.md) has the evidence and its limits.
- M3C's durable campaign, M3D, M3E and M3F are open.

## Verified state

Evidence for the working tree of the commit that proves recursive groups:

- Full gate on the final code: `nix develop -c /usr/bin/time -p scripts/check.sh` returned
  actual exit 0 in 1633.88 s, all 58 stages (`.artifacts/m3b/rec/gate-2.log`). The shared
  rule closer and the audit command changed, so every Nano proof was rebuilt against them
  (library and certificate build 699 s); the full-P4 library and tools took 406 s, of
  which the 132 proof modules are new; `check-coverage --full-p4` checked 256 claims in
  150 s. Nano completion 888 obligations, 0 unresolved, review and release pending under
  the allowance as on every tree after `42ffad6`. Generated Nano output is byte-identical.
  Only the review record and this file were edited after the gate started; the text check
  was rerun on them.
- Not rerun for this commit: the corpus sweep and the four-case replay (evidence is for
  `f329af0`). The executable spec modules are unchanged per the manifest diff, which adds
  118 modules under `Refinement/RunSound/` and changes only the two import roots
  (`P4Spec.lean`, `Refinement.lean`) and `coverage.json`.
- Independent review: [full-P4 review](notes/full-p4/review.md), "Recursive run-soundness
  stage"; no blockers, findings resolved before the commit, not re-reviewed.
- Remote CI: `e0e7863` passed (run 37337844078); not yet run on this commit.

## Open threads and next step

1. Next: M3C's durable record. Extend the shard campaign to the generated worker and a
   larger bound for a CLI-checked record; add rejected programs (negative regressions,
   `p4_16_errors`); commit a generated-code mutation suite for the sweep.
2. Generated `==` converts both operands to IL values (`valueEq`); on the largest programs
   the generated leg is about five times slower than the interpreter. Fix before any
   generated-leg target work (M3D); untried options are in the corpus note.
3. Gate cost roughly doubled on a cold build. On the critical path `Expr_eval`'s relation
   module (195 s) is now followed by its proof module (185 s, 123 s of it symbolic
   execution); the proof build products are about 387 MB, 161 MB for that module, and the
   CI `.lake` cache carries them. Untried: one declaration per relation's induction step,
   which Lean would check in parallel, and smaller proof terms. `check-coverage --full-p4`
   is 150 s because it replans the 98 MB export in the interpreter; a compiled check
   would remove most of it.
4. Run-soundness is one direction for successful runs. The converse, failing runs, and
   any connection of either side to AL belong to M3E and M3F.
5. A warm `lake build` log shows `PANIC at Lean.Meta.whnfEasyCases ... loose bvar` replayed
   as an info message from `NanoP4Spec.Refinement.Reverse.TableEntry_ok` (line 36). The
   module builds and its audits pass; the message predates this work and is unexplained.

## Repository state

M3 work is committed directly on `main`. Preserve local `n3-decl-load`
(`82fbe2e`, non-ancestor WIP), unrelated `docs/repository-review`, and the dirty old
`../p4-spectec-lean-replay` worktree. The expected four-file upstream exporter patch
remains applied; no source pins changed. `.artifacts/p4c` holds the pinned p4c samples.
