# Status

Session handoff, updated 2026-09-27. N3 is authorized and in progress; its first
checkpoint (Program_load/Expr_eval) is partly done. N4–N6 have not started and
full-P4 M3 remains paused.

## Verified checkpoint

N0/N1/N2 are complete (closure `d85e82c`, CI 36316496027). The first N3 checkpoint
adds four commits on `main`: `8ae7998`, `42c3fd3`, `63a95cd` and the review/working-state
follow-up. Paired forward/reverse correspondence now covers 67 of 153 bodied
definitions (39 at N2), with no existing claim statement changed. Details, the
blocker table and the review record are in the
[Nano plan](notes/nano-certification.md#n3-first-checkpoint-in-progress).

Local evidence: full `nix develop -c scripts/check.sh` on the final tree returned
actual exit 0, all 44 stages, no skips (an earlier run failed only text hygiene on
one line, fixed). Remote CI for the pushed revision was pending at handoff; check
it before unrelated work.

## Resume point

Neither N3 entry point is closed. Next, in order:

1. `Decl_load` (Program_load): reapply literal list indexing (`IdxE` on a list
   with a `NumE` index, kept in the ignored `.artifacts/n3/indexing-wip.diff`;
   re-derive it if absent) and profile `Decl_load.refines`, which exceeded
   4M heartbeats. That emits exactly `Decl_load`, `Decls_load`, `Program_load`.
2. Expr_eval: iterated premises in `Expr_eval` and `bin_eq`, then numeric
   function coercions in `un_op`/`bin_op`.
3. Reassess the N3 estimate (now 24–40 hours working range) at the close of
   both entry points.

Iteration cost dominates: any tactic change rebuilds every certificate (about
5 minutes), and a single certificate retry costs 30 seconds to 5 minutes.
Improving this is the next process step; see the plan's reassessment.

## Maintenance and repository state

One worktree on `main`. The older `docs/repository-review` branch and local
archive backup are preserved. The expected upstream exporter patch remains
applied. No source pins changed.
