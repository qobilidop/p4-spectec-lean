# Status

Current checkpoint, updated 2026-09-26.

## Scope

The user authorized settling the next major milestone's scope. Nano-P4 core
semantics and target composition are both required by the new
[design acceptance criteria](../docs/design.md#9-nano-p4-scope-and-acceptance).
README, certification guidance, roadmap and decisions distinguish this target
from delivered coverage. This checkpoint changes documentation only; it does
not begin proof expansion, target integration or broader full-P4 M3.
[Scope evidence](notes/compiler-certification.md#nano-p4-scope-checkpoint)
records review and validation for this change.

## Validation and publication evidence

- Baseline `572975ab68227e5e25e036fd5b57b170ee47e554` passed remote
  [CI run 36272893622](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36272893622),
  verified in this conversation before the scope edits.
- Scope checkpoint: independent read-only review is complete; two scope
  ambiguities were fixed and the reviewer confirmed their resolution.
  Relative link targets and `nix develop -c git diff --check` passed.
  Full `nix develop -c /Users/qobilidop/my/work/p4-spectec-lean/scripts/check.sh`
  passed with actual exit 0, no skips (session 48317,
  `.artifacts/nano-scope-gate.log`). Final documentation evidence updates receive
  text/whitespace checks afterward. No new proof coverage is claimed.
  Publication CI must be matched to this checkpoint's exact SHA in
  [main CI](https://github.com/qobilidop/p4-spectec-lean/actions/workflows/ci.yml).
- Full `nix develop --command scripts/check.sh` passed with actual exit 0,
  no skips (session 6398, `.artifacts/coverage-gate.log`). It includes compiled
  checks of 180 callable entries / 97 claims and eleven rejected mutations.
- Planner tests cover dependency/SCC blockers, covered SCCs, builtin/extern
  boundaries and unchanged stateful refusal. Existing executable and theorem
  sources are unchanged; generated refinement comments now expose SCC blockers.
- Independent final review has no remaining findings. The optional entry-point
  CLI succeeds for `update_fieldValue` and returns exit 1 for an unknown entry.
- The user explicitly reconfirmed direct commit/push on main for this change,
  resolving the conflicting session-supplied PR instruction. Feature commit
  `ffa961cdd9f5e7552dbd20eca45b19cb0fbe2ec0` is on origin/main.
  [Feature CI](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36272406865)
  records that revision's remote result. Any subsequent checkpoint's outcome
  is recorded by [main CI](https://github.com/qobilidop/p4-spectec-lean/actions/workflows/ci.yml);
  match its SHA rather than infer a remote verdict from local checks.
- The generic coverage increment is complete;
  [coverage evidence](notes/coverage.md) retains its detailed review and checks.

## Retained boundaries and next scope

The bounded field-update source connection is complete. Generated Nano
refinement remains 18/153 in one direction; production full-P4 generation and
general reverse automation remain incomplete. Broader M3 stays paused.
[Roadmap](roadmap.md) stages the Nano completion milestone. Next implementation
scope to agree: the complete obligation inventory and feasibility work on
reverse correspondence and Nano target representation. Do not resume broader
M3 or treat this documentation task as authorization to implement the milestone.

The expected four-file upstream export patch remains applied. The finished
`docs/repository-review` branch is retained from the prior refactor; no refs,
worktrees or recovery backups were removed in this scoped pass.
[Archive recovery](notes/archive.md) preserves the local bundle, failed
casting experiment and deliberately discarded ignored-corpus-data boundary.
