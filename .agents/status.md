# Status

Active: full-P4 M3, resumed by the user on 2026-10-04 with autonomous authorization
(decisions, "Scope and product"). The Nano-P4 completion milestone stays closed at
`42ffad6` (2026-09-30); [`notes/nano-release.json`](notes/nano-release.json) records its
review and exact-revision CI for that tree digest.

## Where M3 stands

- M3B is closed: the whole full-P4 export generates as the library `P4Spec` (ignored
  sources, pinned by `P4Spec.manifest.json`, sampled in `P4Spec.samples/`) with executable
  definitions, quotations matching the export, a state-indexed logical relation for each of
  the 256 relations, and an audited run-soundness theorem for every one of them, the 31
  recursion groups included. [Full-P4 overview](notes/full-p4/overview.md) has the
  measurements and what the theorems do not say; decisions, "Recursive state run-soundness
  by fixed-point induction", has the method.
- M3C closed on 2026-10-06 with its durable record ([corpus note](notes/full-p4/corpus.md),
  first three sections): both Lean legs agree with upstream on 1,266 of the 1,267 p4c
  candidates, on upstream's 37 regression programs (13 rejected) and on p4c's 535
  non-excluded error tests (500 typing rejections, 34 parser rejections, one target abort
  on a failed `static_assert`, the first upstream evidence for that branch of the port);
  the regression sweep has a committed six-mutation suite, each mutation rejected by exactly
  the expected programs and statuses; and the shard campaign drives both legs with raised
  bounds and CLI parity (one shard of 64 per leg on the final tool). The one candidate above
  the 1 GiB case bound stays unobserved.
- M3D is in progress: a Lean port of upstream's v1model simulator
  (`P4SpecTec/BackendSim/V1Model/`, with the shared `Hash`, `State`, `Table`, `Stf` and
  `SpecImpl` modules it needs) over explicit spec trampolines, usable by both Lean legs, and
  a session oracle (`P4SpecTecTest/Oracle/P4/Sessions/`) replaying upstream's 199
  non-excluded v1model STF pairs and its 20 regression simulator programs through both
  legs against the pinned upstream simulator. The first session matched on both legs; the
  full run is pending. M3E and M3F are open.

## Verified state

Latest executable validation, for the M3C checkpoint commit (this one; the M3D sources
in progress are not part of it):

- Full gate: `nix develop -c /usr/bin/time -p scripts/check.sh` exit 0 in 457.78 s, all
  59 stages, warm (`.artifacts/m3c/gate-5.log`), on the reviewed text. An earlier run of
  the same tree (`gate-4.log`) passed every stage and then failed with a bash syntax error
  because the gate script was edited while it was running: never edit a shell script a
  running shell is still reading.
- Sweeps on the final tool (every log under `.artifacts/m3c/`): error tests
  (`errors-2.log`) exit 0 in 86 s, 535 of 535 on both legs; regression (`regression-4.log`)
  exit 0, 37 of 37; mutation suite on the reviewed text (`mutations-4.log`) exit 0, six
  mutations rejected; p4c corpus (`corpus-2.log`) exit 0, 1,266 of 1,267 on both legs,
  `switch_p4_16.p4` oversized; shard 0 of 64 on each leg (`shard-*-1.log`) exit 0, 20
  candidates, 40 matches, CLI parity. Not rerun: the four-case replay (evidence is for
  `f329af0`).
- Independent review: [full-P4 review](notes/full-p4/review.md), "M3C durable record
  stage"; no blocker, findings resolved before the commit.
- Nano completion 888 obligations, 0 unresolved, review and release pending under the
  allowance as on every tree after `42ffad6`.

## Open threads and next step

1. Next: M3D. Finish the v1model session sweep on both legs, resolve every disagreement,
   then record it (corpus note, certification table), review, gate and commit; then
   eBPF (upstream's second p4c target, 34 pairs) if the v1model port generalizes cheaply.
2. Generated `==` converts both operands to IL values (`valueEq`); on the largest programs
   the generated leg is about five times slower than the interpreter. Fix before any
   generated-leg target work at scale; untried options are in the corpus note.
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
