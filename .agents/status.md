# Status

Current state only. Updated 2026-09-26.

## Scope

M1/M2 and M3A are closed. The bounded Nano field-update consumer proof is
published (PR #27, implementation `4612534`, main checkpoint `499230b`).
Broader M3 is incomplete and paused. The approved repeatable field-update
certification milestone is implemented and locally validated. Its source
domain and consumer theorem are unchanged; no broader implementation is active.

The requested branch/worktree cleanup and approved README/design consolidation
are complete. PR #28 merged as `d503d36`, preserving documentation commit
`acfa45e`. One primary worktree and only main remain. Retired committed
experiments are in the roughly 7 MB local backup; old ignored artifacts were
intentionally discarded. Recovery scope: `.agents/notes/archive.md`.

## Field-update certification checkpoint

- `Refine/Init.lean` extracts the specification-independent initialization
  proof; the concrete FieldUpdate.Environment API is preserved.
- `FieldUpdate/Certificate.lean` packages typed obligations over the actual
  generated helper, independent source profile and initialized reference.
  Example consumes its composition and commutation fields. Scalar
  representation and finite-fuel realization remain handwritten.
- Colocated `FieldUpdate/test/` runs an unchanged baseline and three mutants:
  wrong update payload rejected by the replayed generated AL-refinement
  proof, renamed quotation rejected by independent export comparison, and
  wrong scalar constructor rejected by representation adequacy. Definitions
  compile before proof challenges; runtime disagreements corroborate the two
  semantic mutants. This is selected artifact sensitivity, not mutation
  coverage of the generator implementation or a generic certificate system.
- Focused warning-failing Lean builds passed (91 jobs), including exact
  axiom audits. Eight runner contract tests and the real mutation suite
  passed locally and independently. Review has no remaining findings:
  `.agents/reviews/field-update-certificate.md`.
- Full `nix develop --command scripts/check.sh`: actual exit 0, no skips,
  session 7692, `.artifacts/field-update-certificate-gate.log` and `.exit`.
  Both 78-program differential legs and all 48 output contexts agree;
  all 342 Nano quotations match. Final status/review wording and EOF hygiene
  were followed by staged whitespace, text and file-size checks.
- Generated sources and pins are unchanged. The expected four-file upstream
  export patch remains applied. Remote CI must pass on the publishing commit
  before completion is reported.

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

## Workflow

The user approved direct commits to main for normal work, optional feature
branches for isolation, and PRs only on explicit request (2026-09-26).
Independent review, the full pre-push local gate and post-push CI remain
required. The operative instructions and in-place decisions agree.

## Next

Pause at this milestone and await a new scope. No broader work is authorized.
Recover experiments only using the archive instructions and preserve the
existing correctness boundaries; do not resume broader M3 automatically.
