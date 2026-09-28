# Status

Session handoff, updated 2026-09-27. N3 (complete core semantics) is authorized
and in progress. The user plans to request completing N3 fully in a new session.
N4–N6 have not started; full-P4 M3 remains paused.

## Verified checkpoint

`main` at `b6f1576` passed remote
[CI 36357022016](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36357022016)
(the two preceding pushes' runs were cancelled as superseded; `b6f1576` contains
them). The full local `nix develop -c scripts/check.sh` returned actual exit 0,
45 stages, no skips, on that tree. Paired forward/reverse correspondence covers 68 of
153 bodied definitions (39 at N2); all 77 relations have run-soundness; the
completion inventory has 888 obligations, 439 bound. The
[Nano plan](notes/nano-certification.md#n3-progress-in-progress) holds the delivered
support, the remaining inventory by file, the blocker table and the reviews.

## Resume point

N3 exit: both directions for all 153 bodied definitions, with representation and
initialization evidence, and the core completion check passing. Next, in order:

1. Calibrate: attempt one or two typing relations (`5.01`) and one evaluation
   rule (`8.01`) with `scripts/replay-cert.py` to see which tactic gaps recur.
2. Expr_eval: continue local branch `n3-expr-eval` (`8ed31d3`): ordered-traversal
   pairing over zipped extracted columns with the recursion hypothesis
   (`bin_eq` → `bin_op` → `Expr_eval`).
3. Program_load: continue local branch `n3-decl-load` (`82fbe2e`): reduce
   `Decl_load`'s proof cost, then split the generated `PARSER` option.
4. Proceed through `Program_ok`, `NanoSwitch_init`, `NanoSwitch_drive` and the
   remaining sweep per the plan's N3 section.

Both WIP branches are local only, rebased onto `b6f1576` as hand-written changes;
regenerate `NanoP4Spec/` after checking one out. Iterate on tactics with
`scripts/replay-cert.py` (faithful only for tactic-only changes; never evidence).

## Maintenance and repository state

One worktree on `main`. Local branches: `n3-decl-load`, `n3-expr-eval` (WIP above)
and the older `docs/repository-review`; the local archive backup is preserved.
The expected upstream exporter patch remains applied. No source pins changed.
