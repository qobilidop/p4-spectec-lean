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
- M3C, regression sweep (2026-10-05): both legs agree with upstream on its 37 regression
  programs, 13 of them rejected (typing failures; twelve beyond the one the bounded replay
  already had).
- M3C's durable campaign and mutation suite, M3D, M3E and M3F are open.

## Verified state

The compaction commit of 2026-10-06 changes documents and working state only (no
executable input): it reuses the gate recorded for `0d78b6e` below, with the text check
(exit 0) and a relative-link check of every edited document rerun, and its own review
("Working-state compaction" in the review note).

Evidence for `0d78b6e`, the commit that adds the regression sweep (Python harness and
documents only; no Lean source changed since `00aa1c2`):

- Full gate on the final files: `nix develop -c /usr/bin/time -p scripts/check.sh`
  returned actual exit 0 in 397.51 s, all 58 stages (`.artifacts/m3c/gate-2.log`), warm:
  every Lean module was already built from the `00aa1c2` gate. Only this file was edited
  afterwards; the text check was rerun.
- Regression sweep on the final tool: exit 0, 37 of 37 on both legs, in about 40 s
  (`.artifacts/m3c/regression-3.log`, summary under `.artifacts/p4-regression-sweep/`).
- p4c corpus sweep rerun on the final tool, since its capture path changed: exit 0 in
  1,240 s, 1,266 of 1,267 `matched,matched` on both legs, `switch_p4_16.p4` unobserved
  (oversized), as before (`.artifacts/m3c/corpus-1.log`). This is also the first sweep of
  the library generated at `00aa1c2`, whose executable modules are unchanged.
- Not rerun: the four-case replay (evidence is for `f329af0`).
- Independent review: [full-P4 review](notes/full-p4/review.md), "Regression sweep stage";
  no blockers, findings resolved before the commit, not re-reviewed.
- For `00aa1c2` (run-soundness for every relation): full gate exit 0 in 1633.88 s, 58
  stages, cold for every proof (`.artifacts/m3b/rec/gate-2.log`); review "Recursive
  run-soundness stage". Nano completion 888 obligations, 0 unresolved, review and release
  pending under the allowance as on every tree after `42ffad6`.
- Remote CI: `0d78b6e` passed (run 37365938053), building the 132 proof modules on the
  runner; the `00aa1c2` run was cancelled as superseded. Not yet run on the compaction
  commit.

## Open threads and next step

1. Next: M3C's durable record. Extend the shard campaign to the generated worker and a
   larger bound for a CLI-checked record, and commit a generated-code mutation suite for
   the sweeps (the regression set runs in 40 s and includes rejections, which makes it the
   cheap target for mutations). p4c's `p4_16_errors` needs the restore and the inventory
   extended to it and to upstream's 52 negative exclusion references.
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

## Working-state compaction (2026-10-06)

A tend-repo pass after M3B's close: the decisions register's full-P4 entries were
rewritten to what is true now and the closed Nano entries merged into one; the full-P4
overview records M3B as a closed stage with its measurements; the five earlier M3 stage
reviews are tabulated with their revisions, findings and limits (prose at `0d78b6e`). An
independent review of the pass found no lost obligation; three figures that had drifted
and the rejected alternatives it found missing were restored before the commit. Learned: a pre-gate `check-text`/`--wfail` rule in AGENTS, and proof
profiling guidance in `docs/performance.md`. Resume read is about 1,160 lines, mostly
`docs/design.md` and the register.

## Repository state

M3 work is committed directly on `main`. Preserve local `n3-decl-load`
(`82fbe2e`, non-ancestor WIP), unrelated `docs/repository-review`, and the dirty old
`../p4-spectec-lean-replay` worktree. The expected four-file upstream exporter patch
remains applied; no source pins changed. `.artifacts/p4c` holds the pinned p4c samples.
