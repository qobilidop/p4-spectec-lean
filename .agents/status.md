# Status

N4 target composition implemented, 2026-09-29, on branch `n4-target` (user-authorized the
same day). The completion check now verifies every core and target obligation; the four
release-stage obligations (N5 consumer proof, N6 sensitivity, review, release) remain.
Full-P4 M3 remains paused.

## Verified state

- The interpreter passes its own function evaluator, at the remaining fuel, to extern
  relations; `NanoP4Target.externsContractHolds` discharges `NanoP4Spec.externsContract`
  for the concrete NanoSwitch target in both directions for every related input.
- `NanoP4Target.sessionCorrespondence` composes `NanoSwitch_init` with packet driving in both
  directions; the initialized-environment corollary and `sessionObservations` are checked
  by `check-target` with exact types, plus a witness that the reference configuration is
  inhabited and that the pinned export declares no print hints.
- All 78 typing programs match upstream on both legs; all 39 STF sessions (74 packets) match
  upstream at every step on both Lean paths (`check-nano-sessions`, six mutations rejected).
- `scripts/nano-certification.py --require-n2 --require-owned N4` and
  `--require-complete target` report 888 obligations, 766 compiled claim bindings and 0
  unresolved; replay cases are verified by the checker's own runs.

## Commits on `n4-target`

`e88e8a0` extern discharge; `ad1c4ab` sessions and corpus replay; `09cb951` replay
hardening; `a0f7c79` completion binding; then review fixes and this checkpoint. Reviews are
recorded in the [target note](notes/nano-target.md#n4-review-record).

## Validation

Full gate on `a0f7c79` (`.artifacts/n4-gate-2.log`): 46 of 47 stages exit 0 in 167s;
text hygiene failed on one over-long line in `Tools/CheckTarget.lean`, since fixed. The
completion stage passed with 0 unresolved. The final full gate for the merged revision is
recorded below when run.

## Next steps

1. Final full gate, merge `n4-target` into `main`, push, and confirm exact-revision CI
   (milestone completion requires it).
2. N5 (whole-program theorem) needs a separate user scope. The candidate is
   `positive/src-addr-filter.p4`, whose session the replay already covers; build it on
   `NanoP4Target.initializedSessionCorrespondence`.

## Repository state

Preserve local `n3-decl-load` (`82fbe2e`, non-ancestor WIP), unrelated
`docs/repository-review`, and the dirty old `../p4-spectec-lean-replay` worktree. The
expected four-file upstream exporter patch remains applied; no source pins changed.
