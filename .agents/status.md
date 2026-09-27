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

1. `Decl_load` (Program_load): continue from local branch `n3-decl-load`
   (`6996172`, WIP, unvalidated; its commit message lists what it holds and
   lacks). It admits literal list indexing and gets `Decl_load.refines` as far as
   the `find_callableDef_l` call at 8M heartbeats (~5 minutes per replay): the
   reference `PARSER` option is exposed as `none` while the generated `p0.PARSER`
   is not split to match. Address proof performance (seven paths over very large
   reference values) before the remaining gaps.
2. Expr_eval: iterated premises in `Expr_eval` and `bin_eq`, then numeric
   function coercions in `un_op`/`bin_op`.
3. Reassess the N3 estimate (now 24–40 hours working range) at the close of
   both entry points.

Tactic iteration: use `scripts/replay-cert.py` (added after `3b74f2e`) instead of
`lake build` for single certificates; it re-elaborates scratch copies against
existing generated object files (for example 28 seconds for
`Parameters_ok --only realizes`) and `refine_al.trace` now names the goal on which
a resource limit ran out. It is faithful only for tactic-only changes and is not
evidence; the full gate remains the verdict. Its commit passed the full local gate
(actual exit 0, 45 stages, no skips) after independent review fixes; CI for `3b74f2e`
was still running at that point and the tooling push follows it.

## Maintenance and repository state

One worktree on `main`; local branch `n3-decl-load` holds the WIP above. The
older `docs/repository-review` branch and local
archive backup are preserved. The expected upstream exporter patch remains
applied. No source pins changed.
