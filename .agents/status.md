# Status

Current state only. Updated 2026-09-26.

## Scope

M1/M2 and M3A are closed. The bounded Nano field-update consumer proof is
published (PR #27, implementation `4612534`, main checkpoint `499230b`).
Broader M3 is incomplete and paused. No implementation work is active.

The requested branch/worktree cleanup and approved README/design consolidation
are complete. PR #28 merged as `d503d36`, preserving documentation commit
`acfa45e`. No Lean code, pin, export or gate changes.

## Consolidation checkpoint

- One worktree remains: `/Users/qobilidop/my/work/p4-spectec-lean`.
  All eighteen secondary checkouts were removed after lossless archival.
- The first conservative cleanup retained too many historical refs/checkouts.
  The stronger request superseded that policy: retain recovery data externally,
  not as active development state. See `.agents/notes/archive.md`.
- All original branch tips are in a self-contained verified bundle. The user
  chose to discard the 24 GiB folder snapshot and redundant verification mirror,
  keeping only the roughly 7 MB committed-history backup and small metadata.
- The stale integration cherry-pick was closed with `--quit`, not `--abort`,
  after archiving its sequencer. HEAD, index bytes and clean source state were
  unchanged. Its code was already integrated; no proof work was resumed.
- All old local refs were removed after matching the verified backup. Only
  main remains locally and on GitHub; the consolidation branch was deleted
  after its PR merged, and fresh local/remote inventories verified its absence.
  All 23 old non-main GitHub refs were deleted with one atomic, exact-SHA-guarded
  push after the full local gate passed. Every tip was merged and no open PR
  existed. The final cleanup inventory shows only main at `d503d36`.
- Selective documentation reconciliation preserves newer main decisions and
  checked-runtime boundaries. The consumer example is complete; bounded packet
  support is not a complete target. Independent reviews:
  `.agents/reviews/project-state-docs.md` and
  `.agents/reviews/project-state-archive.md`.
- Fresh `nix develop --command scripts/check.sh` completed with actual exit 0,
  no skips, recorded in `.artifacts/consolidation-gate.log` and its `.exit`
  file. Final backup/status wording was then updated and hygiene rechecked.
  Final-head remote Gate `36229832016` passed on `acfa45e`, including both
  upstream pin checks. PR #28 is merged and its temporary branch is removed.
  The expected four-file upstream export patch remains applied.
- The routine postmerge handoff passed the complete local gate again: actual
  exit 0, no skips, `.artifacts/consolidation-handoff-gate.log` and `.exit`
  (session 53505). Independent handoff review found no issues; the final
  result-only status addition was followed by staged hygiene checks.

## Archived, not completed

Production aggregate `925fdbf`, source integration `1b2ac70`, still fails
the second full-P4 casting proof at the unchanged 4M heartbeat limit. Earlier
experiments are integrated, superseded or represented in this aggregate.
Archiving them is not a full-P4 completion or integration claim.

Frozen corpus `c4a8858` stopped with exit 130 after shards 0-44: 180 attempts,
338 AL matches and eleven oversized-artifact failures. These are partial
historical totals, not a whole-corpus result. Raw campaign artifacts were
intentionally discarded with the large backup. Exact resume is not available
from the committed-history bundle; any new run requires fresh scope and evidence.

The completed consumer proves distinct-name field-update commutation through
actual generated/reference correspondence on its scalar domain, discharging
representation, initialization and finite reference-fuel obligations. It does
not certify arbitrary assignment reordering, all Nano-P4 or full P4.

## Workflow update

The user approved direct commits to main for normal work, optional feature
branches for isolation, and PRs only on explicit request (2026-09-26).
Independent review, the full pre-push local gate and post-push CI remain
required. AGENTS, the in-place decisions and the design's checkpoint rule
now agree; no implementation changed. Independent review found no remaining
issues (`.agents/reviews/direct-commit-workflow.md`). The complete local gate
exited 0 with no skips (session 25817), recorded in
`.artifacts/direct-commit-workflow-gate.log` and `.exit`. Final documentation
and review wording was followed by staged whitespace, text and size checks.
Remote CI is checked on the published commit before declaring completion.

## Next

Await the user's revised development plan. No implementation work is active.
Recover experiments only using the archive instructions and preserve the
existing correctness boundaries; do not resume broader M3 automatically.
