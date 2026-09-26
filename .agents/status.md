# Status

Current state only. Updated 2026-09-26.

## Scope

M1/M2 and M3A are closed. The bounded Nano field-update consumer proof is
published (PR #27, implementation `4612534`, main checkpoint `499230b`).
Broader M3 is incomplete and paused. No implementation work is active.

The user requested closing all obsolete branches and worktrees. Approved
README/design documentation is being consolidated onto current main through
`consolidate-project-state`. No Lean code, pin, export or gate changes.

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
  main and the temporary consolidation branch remain until publication.
  All 23 old non-main GitHub refs were deleted with one atomic, exact-SHA-guarded
  push after the full local gate passed. Every tip was merged and no open PR
  existed. Fresh remote inventory shows only main at `499230b`.
- Selective documentation reconciliation preserves newer main decisions and
  checked-runtime boundaries. The consumer example is complete; bounded packet
  support is not a complete target. Independent reviews:
  `.agents/reviews/project-state-docs.md` and
  `.agents/reviews/project-state-archive.md`.
- Fresh `nix develop --command scripts/check.sh` completed with actual exit 0,
  no skips, recorded in `.artifacts/consolidation-gate.log` and its `.exit`
  file. Final backup/status wording was then updated and hygiene rechecked.
  Consolidation PR publication and remote CI remain pending at this checkpoint.
  The expected four-file upstream export patch remains applied.

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

## Next

Finish the consolidation PR and delete its temporary branch, leaving only main.
Then await the user's revised development plan. Recover experiments only using
the archive instructions and preserve the existing correctness boundaries.
