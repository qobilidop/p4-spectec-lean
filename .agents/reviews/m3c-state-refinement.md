# Bounded stateful function refinement review

Reviewer: independent root Codex agent, not the implementing subagent.
Reviewed implementation: `de73566`, frozen `m3c-state-refinement` worktree.
Date: 2026-09-25. This is AI-agent review, not human review.

The reviewer read all new modules and the actual-emission fixture:
`Codegen.StateValidate`, `Refine.StateNormalize`, `Tactic.StateRefine`, and
`P4SpecTecTest.StateValidate`. The reviewer directly re-elaborated the latter
in the pinned environment in
`/Users/qobilidop/my/work/p4-spectec-lean-state-refinement`; the Lean command
exited 0. The review did not rely only on the implementing agent's build.

No correctness findings in the bounded all-fuel, all-outcome exact-state
contract. The calculus preserves consumed state through both failure kinds,
ordered fallback, and modular calls. The fixtures exercise actual executable
and theorem emission, not only handwritten analogues. Generated proofs are
axiom-audited, and unsupported tactic shapes fail without recovery.

Integration requirement: production selection must propagate recursive-group
and dependency exclusions. Comment-only output from `groupTheorems` is not
proof coverage and must never mark such groups covered. Production Emit is
outside this PR, so that requirement remains an integration obligation, not a
claim about code delivered here. Full-P4 scalability and wider proof support
also remain open.

The PR branch ports the reviewed implementation onto merged main `b08ab8e`,
preserves the existing emitted-fresh fixture import, and updates status and
inherited interpreter-boundary notes. No semantic implementation changes were
made during that port. The implementing agent subsequently ran the full
pinned `scripts/check.sh` on the PR tree: exit 0, no skips. This is integration
validation, separate from the reviewer's direct check. Remote CI remains
required before merge.
