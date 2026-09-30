# Status

N5 (whole-program theorem) implemented on local branch `n5-consumer`, 2026-09-30, and under
review-fix validation; the user authorized completing the Nano-P4 milestone (N5 and N6) fully
autonomously the same day. N4 is complete on `main` (`4535868`,
[CI 36592809255](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36592809255)).
Full-P4 M3 remains paused.

## Verified state (branch)

- `lazy_eval` evaluates generated code with kernel-checked proofs (decisions, "N5 whole-program
  evidence"); `ExampleProofs/NanoP4SrcAddrFilter/` proves that every three-byte packet on every
  host-range port is forwarded unchanged exactly when its source address is 1 or 2, shorter
  packets are dropped, and pins the STF session's trace; `referenceFilter` transfers the property
  to the reference interpreter. The only premise is `NanoP4Target.PacketStateText`.
- `check-consumer`: identity, the whole STF trace against upstream, literal values, 7 claims.
- `--require-owned N5` completion: 888 obligations, 767 compiled claim bindings, 0 unresolved.
- The mutation suite rejects six mutations; the receiver mutation is rejected by the extern
  contract, since extract's receiver is discarded by the parser ([note](notes/nano-consumer.md)).

## Commits on `n5-consumer`

`24d36aa` evaluator; `4c9dcb8` packet families and transmissions; `a8136b1` program quotation;
`62f41b7` whole-program example and checker; `994659b` gate and completion binding; `d7fac98`
documentation; the review-resolution commit follows.

## Validation

- `d7fac98`: full `nix develop -c /usr/bin/time -p scripts/check.sh` returned actual exit 0 in
  189.86s, all 50 stages (`.artifacts/n5-gate-1.log`).
- Review fixes (uncommitted at this writing): example, tool and test builds, `lake test`,
  `check-consumer`, the runner (six rejections) and its contract tests, and the completion CLI
  tests exit 0. The full gate must rerun on the resolution commit.

## Next steps

1. Commit the review resolutions, rerun the full gate, and have the reviewer confirm the fixes.
2. Merge `n5-consumer` into `main`, push, record CI.
3. N6 (plan, `notes/nano-certification.md#n6-close-release-evidence`).

## Repository state

Preserve local `n3-decl-load` (`82fbe2e`, non-ancestor WIP), unrelated
`docs/repository-review`, and the dirty old `../p4-spectec-lean-replay` worktree. The
expected four-file upstream exporter patch remains applied; no source pins changed.
