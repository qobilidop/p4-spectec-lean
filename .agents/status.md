# Status

N6 (release evidence) implemented and reviewed on branch `n6-release`, 2026-09-30; the user
authorized completing the Nano-P4 milestone (N5 and N6) fully autonomously the same day. N5 is
complete on `main` (`034a90b`,
[CI 36692276571](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36692276571)).
Full-P4 M3 remains paused.

## Verified state (branch)

- The gate requires `--require-n2 --require-complete all --allow-unpublished`: 888 obligations,
  0 unresolved; only the review and release records may be pending
  ([release note](notes/nano-release.md), decisions "N6 release evidence").
- Sensitivity: the completion check runs the field-update, source-address filter and
  cross-layer mutation suites; the cross-layer suite rejects five mutations at named checks.
- Release costs: `docs/performance/nano-release-2026-09-30.md`.

## Commits on `n6-release`

`3841877` cross-layer mutations; `4e2555a` combined completion in the gate; `551df89` docs;
`a146d78`, `868cc81` review resolutions; `5ebec11` performance snapshot; `d5c4b17` working
state; `5eefa3f`, `883ebca` delta-review resolutions; the following commit records them.

## Validation

- `868cc81`: full `nix develop -c /usr/bin/time -p scripts/check.sh` returned actual exit 0 in
  255.46s, all 49 stages (`.artifacts/n6-gate-1.log`). `5ebec11` adds only documentation.

## Next steps

1. Confirm the delta resolutions with the reviewer; full gate at the branch tip.
2. Fast-forward `main`, push, wait for exact-revision CI.
3. Evidence commit: `notes/nano-release.json` naming the reviewed revision, gate and CI; check
   `--require-complete all` passes without the allowance; push; compact `.agents/`.

## Repository state

Preserve local `n3-decl-load` (`82fbe2e`, non-ancestor WIP), unrelated
`docs/repository-review`, and the dirty old `../p4-spectec-lean-replay` worktree. The
expected four-file upstream exporter patch remains applied; no source pins changed.
