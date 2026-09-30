# Status

N4 target composition complete, 2026-09-29 (user-authorized the same day), merged to `main`
at `4535868` with passing exact-revision
[CI 36592809255](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36592809255). The completion check now verifies every core and target obligation; the four
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
hardening; `a0f7c79` completion binding; `1f9d6bd` evidence tightening; `713fef2` and the
following commit record the checkpoint. Four independent read-only AI reviews and their
resolutions are in the [target note](notes/nano-target.md#n4-review-record).

## Validation

- `a0f7c79`: full gate 46 of 47 stages exit 0 (text hygiene failed on one line, fixed).
- `713fef2`: full `nix develop -c /usr/bin/time -p scripts/check.sh` returned actual exit 0
  in 154.85s, all 47 stages, no skips (`.artifacts/n4-gate-3.log`).
- `22fc21c` (review resolution, code and documentation): full
  `nix develop -c /usr/bin/time -p scripts/check.sh` returned actual exit 0 in 156.45s, all
  47 stages, no skips (`.artifacts/n4-gate-5.log`). An earlier attempt at that commit failed
  one axiom `#guard_msgs` expectation and was amended before publication.
- `4535868` (final evidence commit, reusing that gate with a fresh text check) passed
  remote [CI 36592809255](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36592809255).
  The merged `n4-target` branch was local only and is deleted.

## Maintenance

A general tend-repo pass after N4 (documentation and working state only) compacted the
Nano plan and roadmap, repaired anchors and corrected the target oracle README; see the
[stewardship note](notes/repository-stewardship.md#current-maintenance-pass). It reuses
`22fc21c`'s exit-0 full gate (executable inputs unchanged) with fresh text and link
checks, and an independent read-only Claude Opus review whose findings were adopted.

## Next steps

1. N5 (whole-program theorem) needs a separate user scope. The candidate is
   `positive/src-addr-filter.p4`, whose session the replay already covers; build it on
   `NanoP4Target.initializedSessionCorrespondence`.

## Repository state

Preserve local `n3-decl-load` (`82fbe2e`, non-ancestor WIP), unrelated
`docs/repository-review`, and the dirty old `../p4-spectec-lean-replay` worktree. The
expected four-file upstream exporter patch remains applied; no source pins changed.
