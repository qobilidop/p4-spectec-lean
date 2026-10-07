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

Latest executable validation, for `0d78b6e` (regression sweep; Python harness and
documents only, no Lean source changed since `00aa1c2`):

- Full gate: `nix develop -c /usr/bin/time -p scripts/check.sh` exit 0 in 397.51 s, all
  58 stages, warm (`.artifacts/m3c/gate-2.log`). For `00aa1c2`, the same gate cold for
  every proof module: exit 0 in 1633.88 s (`.artifacts/m3b/rec/gate-2.log`). Nano
  completion 888 obligations, 0 unresolved, review and release pending under the
  allowance as on every tree after `42ffad6`.
- Sweeps on the final tool: regression, exit 0, 37 of 37 on both legs
  (`.artifacts/m3c/regression-3.log`); p4c corpus, exit 0 in 1,240 s, 1,266 of 1,267 on
  both legs, `switch_p4_16.p4` oversized (`.artifacts/m3c/corpus-1.log`). Not rerun: the
  four-case replay (evidence is for `f329af0`).
- Independent reviews: [full-P4 review](notes/full-p4/review.md), "Recursive
  run-soundness stage" and "Regression sweep stage"; no blockers, findings resolved
  before the commits.
- Remote CI: `0d78b6e` passed (run 37365938053), building the 132 proof modules on the
  runner.

The two tend-repo commits of 2026-10-06 change documents, working state and one comment
in `scripts/nano-certification.py`. CI for the first (`0e4b521`, run 37573527725)
passed. The second's full gate, run because it touches a
script: `nix develop -c /usr/bin/time -p scripts/check.sh` exit 0 in 417.73 s, all 58
stages, warm (`.artifacts/tend/gate-1.log`); only documents and the skill were edited
afterwards, with the text and link checks rerun. Review: "Working-state compaction" in
the review note (both passes).

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

Two tend-repo passes after M3B's close rewrote the decisions register to what holds now
(full-P4 entries; the closed Nano entries merged into two), recorded M3B in the full-P4
overview as a closed stage, tabulated the five earlier stage reviews, and replaced the two
closed performance notes by `notes/performance-history.md`; prose of all of them is at
`0e4b521` and before. Learned, where it applies: a pre-gate text and warning check
(AGENTS), proof profiling (`docs/performance.md`), and two weaknesses of the procedure
itself (the skill). Resume read: status, decisions, design and pitfalls, about 1,180
lines, of which `docs/design.md` is 491.

## Repository state

M3 work is committed directly on `main`. Preserve local `n3-decl-load`
(`82fbe2e`, non-ancestor WIP), unrelated `docs/repository-review`, and the dirty old
`../p4-spectec-lean-replay` worktree. The expected four-file upstream exporter patch
remains applied; no source pins changed. `.artifacts/p4c` holds the pinned p4c samples.
