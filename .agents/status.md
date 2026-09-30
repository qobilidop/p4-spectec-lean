# Status

Nothing is active. The Nano-P4 completion milestone (design section 9) closed on 2026-09-30 at
`42ffad6`: the gate requires every proof, replay, consumer and sensitivity obligation, and
[`notes/nano-release.json`](notes/nano-release.json) records the independent review and the
exact-revision [CI 36697907550](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36697907550)
for its tree digest. Full-P4 M3 remains paused. Ask the user for a scope before starting new work.

## Verified state

- `scripts/nano-certification.py --require-n2 --require-complete all --allow-unpublished` (the
  gate): 888 obligations, 0 unresolved. Without the allowance, `--require-complete all` passes
  on this tree; any change outside `.agents/` leaves review and release pending until re-recorded.
- Evidence, audit, costs and reviews: [release note](notes/nano-release.md); N5 in the
  [consumer note](notes/nano-consumer.md); stage index in the
  [plan](notes/nano-certification.md#closed-stages).

## Validation

- `42ffad6`: full `nix develop -c /usr/bin/time -p scripts/check.sh` with the extracted exports
  removed first returned actual exit 0 in 219.95s, all 49 stages; exact-revision CI passed.
- The evidence commit after it changes only `.agents/`; checked with
  `scripts/nano-certification.py --require-n2 --require-complete all` (no allowance).

## Repository state

Branch `n6-release` is merged into `main`; delete it once the evidence commit's CI passes.
Preserve local `n3-decl-load` (`82fbe2e`, non-ancestor WIP), unrelated
`docs/repository-review`, and the dirty old `../p4-spectec-lean-replay` worktree. The
expected four-file upstream exporter patch remains applied; no source pins changed.
