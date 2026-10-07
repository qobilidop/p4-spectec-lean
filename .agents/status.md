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
  measurements and what the theorems do not say.
- M3C closed on 2026-10-06 ([corpus note](notes/full-p4/corpus.md), first three sections):
  both Lean legs agree with upstream on 1,266 of the 1,267 p4c candidates, on upstream's 37
  regression programs and on p4c's 535 non-excluded error tests; the regression sweep has a
  committed six-mutation suite; the shard campaign drives both legs.
- M3D closed on 2026-10-07 (corpus note, "Packet targets"): Lean ports of upstream's
  v1model and eBPF simulators (`P4SpecTec/BackendSim/`), generic in the spec they call back
  into, run on both Lean legs against upstream's own simulator on every STF session of its
  p4c-sample and regression sets, 219 v1model and 15 eBPF, every event at the
  architecture's boundary matching. Getting there needed upstream's result cache mirrored
  as a semantics-transparent memoization (`Prelude/Memo.lean`; decisions, "Memoized
  relation runs"): proofs see the uncached run by definition, the executable caches, and
  the exponential re-evaluation of rule groups like `TableKeys_eval` is gone. Not covered:
  PSA (no runnable upstream pair at the pin), upstream's five custom v1model sessions and
  its p4testgen sets, statements no session exercises.
- M3E and M3F are open. The explicit-state refinement fragment admits none of the 747
  full-P4 functions and builtins (overview, obligation 4, with the census by reason); with
  its scalar restriction lifted it would admit 11 of 700 functions, the rest stopped by
  non-variable clause patterns (252), expressions outside the fragment (250) and builtin
  calls (132), and `P4Spec` has no representation certificates to state a non-scalar
  theorem with. Closing M3E is the pure forward calculus (`refine_al`) brought to the
  stateful carrier plus full-P4 representation certificates: work on M3B's scale.

## Verified state

Latest executable validation, for the M3D checkpoint (this tree):

- Full gate: `nix develop -c /usr/bin/time -p scripts/check.sh` exit 0 in 400.15 s, all
  60 stages, warm (`.artifacts/m3c/gate-7.log`), on the reviewed text after the census
  was regenerated for the memoizing generator; the preceding run of the same tree
  (`gate-6.log`, 911 s with the final rebuild) failed only that stale-census stage.
- Final-tool sweeps, every log under `.artifacts/m3c/`, every exit 0: v1model sessions
  219 of 219 on both legs in 664 s (`sessions-v1model-5.log`); eBPF sessions 15 of 15 in
  56 s (`sessions-ebpf-5.log`); regression 37 of 37 (`regression-7.log`); error tests 535
  of 535 (`errors-4.log`); p4c corpus 1,266 of 1,267, `switch_p4_16.p4` oversized
  (`corpus-4.log`). The gate's mutation suite ran on the same workers. Not rerun: the
  four-case replay (evidence is for `f329af0`) and the shard campaign (its tool changed
  only by the memoization, which the sweeps cover).
- Independent review: [full-P4 review](notes/full-p4/review.md), "M3D packet targets and
  memoization stage": one blocker and six should-fix findings, all resolved before the
  commit and covered by the reruns above; the naming deviation of `BackendSim/` modules
  from upstream's paths is accepted and recorded.
- Nano completion 888 obligations, 0 unresolved, review and release pending under the
  allowance as on every tree after `42ffad6`; Nano regeneration is unchanged by the
  memoizing generator (its mode is pure).

## Open threads and next step

1. Next: M3E, as a first slice that can be stated and audited: emit representation
   certificates for the full-P4 types the pure emitter already handles, then admit the
   first-order functions with non-scalar parameters and results whose bodies the fragment
   accepts (11 today), and measure `state_refine_al` on them before widening to clause
   patterns and the general expression language. Propagate exclusions through callees;
   comment-only output is not coverage.
2. Generated `==` converts both operands to IL values (`valueEq`); on the largest programs
   the generated leg is about five times slower than the interpreter. Memoization did not
   change this. Untried options are in the corpus note.
3. Gate cost: 400 s warm (`gate-7.log`), 911 s with the final rebuild (`gate-6.log`);
   the critical path is unchanged (`Expr_eval`'s relation and proof modules). Untried:
   one declaration per induction step; a compiled coverage check.
4. Run-soundness is one direction for successful runs; the converse and failing runs
   belong to M3E and M3F.
5. The memo cache clears when full where upstream evicts by a clock; no sweep has hit the
   capacity in a way that mattered. Objects reachable from the cache pay atomic reference
   counts afterwards; the session legs run in seconds, so this was not measured.
6. `BackendSim/V1Model/`, `Stf/{Ast,Transform}.lean` and the per-target `Stf.lean`
   modules deviate from upstream's paths (corpus note, "Packet targets"); rename when the
   mirror check gains `BackendSim` as a root.
7. A warm `lake build` log shows `PANIC at Lean.Meta.whnfEasyCases ... loose bvar` replayed
   as an info message from `NanoP4Spec.Refinement.Reverse.TableEntry_ok` (line 36). The
   module builds and its audits pass; the message predates this work and is unexplained.

## Lessons kept (2026-10-07)

A background wrapper's exit is not the build's: record the build's own exit in its log and
read that. One Dune build at a time: two sweeps each rebuilding upstream abort each other.
The text gate reads tracked files only: check untracked Lean before a commit. An object in
a module-initialized cell is never exclusive to the runtime (pitfalls).

## Repository state

M3 work is committed directly on `main`. Preserve local `n3-decl-load`
(`82fbe2e`, non-ancestor WIP), unrelated `docs/repository-review`, and the dirty old
`../p4-spectec-lean-replay` worktree. The expected four-file upstream exporter patch
remains applied; no source pins changed. `.artifacts/p4c` holds the pinned p4c samples;
`.artifacts/p4-sessions-sweep/<arch>/` the session observations and summaries.
