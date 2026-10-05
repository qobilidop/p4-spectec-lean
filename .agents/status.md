# Status

Active: full-P4 M3, resumed by the user on 2026-10-04 with autonomous authorization
(decisions, "Scope and product"). The Nano-P4 completion milestone stays closed at
`42ffad6` (2026-09-30); [`notes/nano-release.json`](notes/nano-release.json) records its
review and exact-revision CI for that tree digest.

## Where M3 stands

- M3B: the whole full-P4 export generates as the library `P4Spec` (ignored sources,
  pinned by `P4Spec.manifest.json`, sampled in `P4Spec.samples/`): executable definitions,
  quotations matching the export, a state-indexed logical relation for each of the 256
  relations, and since 2026-10-05 an audited run-soundness theorem for the 14 relations
  that reach no recursive relation. M3B's exit needs the other 242.
  [Full-P4 overview](notes/full-p4/overview.md) has the measurements and what is missing.
- M3C, sweep (`f329af0`): the generated library and the reference interpreter both agree
  with upstream on 1,266 of the 1,267 corpus candidates, for typing and instantiation.
  [Corpus note](notes/full-p4/corpus.md) has the evidence and its limits.
- M3C's durable campaign, M3D, M3E and M3F are open.

## Verified state

Evidence for the working tree of the commit that adds run-soundness:

- Full gate, after the review resolutions: `nix develop -c /usr/bin/time -p
  scripts/check.sh` returned actual exit 0 in 444.33 s, all 58 stages
  (`.artifacts/m3b/rs-gate-2.log`), including every Nano proof rebuilt against the
  changed shared tactic helper, the 14 `RunSound` modules, and the new stage
  `check-coverage --full-p4` (14 claims, about 113 s). Nano completion 888
  obligations, 0 unresolved, review and release pending under the allowance as on every
  tree after `42ffad6`. Generated Nano output is byte-identical.
- Not rerun for this commit: the corpus sweep and the four-case replay (evidence is for
  `f329af0`). The executable spec modules are unchanged per the manifest diff.
- Independent review: [full-P4 review](notes/full-p4/review.md), "Run-soundness stage";
  no blockers, should-fix items resolved before the commit, not re-reviewed.
- Remote CI: `916c7ba` (golden samples) and `c7ed36f` passed; not yet run on this commit.

## Open threads and next step

1. Next: recursive run-soundness (M3B's exit), following decisions, "Recursive state
   run-soundness: planned shape". Order: the generic realization step as a library lemma
   and tactic, with the `RecursivePrefix` fixture reproved through it; attempt transport
   by Lean's `monotonicity`; a generator for one small recursive full-P4 group
   (`ParserStmt_ok`, five relations); then measure `Cast_impl` and `Expr_eval`.
2. M3C: extend the shard campaign to the generated worker and a larger bound for a
   durable, CLI-checked record; add rejected programs (negative regressions,
   `p4_16_errors`); commit a generated-code mutation suite for the sweep.
3. Generated `==` converts both operands to IL values (`valueEq`); on the largest programs
   the generated leg is about five times slower than the interpreter. Fix before any
   generated-leg target work (M3D); untried options are in the corpus note.
4. Gate cost: `check-coverage --full-p4` adds 113 s because it replans the 98 MB export in
   the interpreter, and `Expr_eval`'s relation module is 195 s of a cold build. Neither
   blocks work; a compiled coverage check would remove the first.
5. A warm `lake build` log shows `PANIC at Lean.Meta.whnfEasyCases ... loose bvar` replayed
   as an info message from `NanoP4Spec.Refinement.Reverse.TableEntry_ok` (line 36). The
   module builds and its audits pass; the message predates this work and is unexplained.

## Repository state

M3 work is committed directly on `main`. Preserve local `n3-decl-load`
(`82fbe2e`, non-ancestor WIP), unrelated `docs/repository-review`, and the dirty old
`../p4-spectec-lean-replay` worktree. The expected four-file upstream exporter patch
remains applied; no source pins changed. `.artifacts/p4c` holds the pinned p4c samples.
