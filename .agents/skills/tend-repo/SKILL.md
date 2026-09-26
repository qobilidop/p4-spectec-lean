---
name: tend-repo
description: Maintain this repository on request by checking consistency, compacting .agents working state, and preserving evidence-backed lessons. Use for repository upkeep or retrospective cleanup, not ordinary feature implementation or an unsolicited whole-repo rewrite.
---

# Tend repo

Leave the repository easier to understand and resume, without growing its
instructions by default. Follow `AGENTS.md` for policy, environment, review
and publication requirements; this skill supplies a maintenance procedure,
not a second policy source. Paths below are relative to the repository root.

## Establish the scope and evidence

Read the resume files in the order prescribed by `AGENTS.md`. Inspect the
working tree, current commit, active work and recent relevant history before
editing. Preserve unrelated work and the expected upstream patch.

Honor a narrower request such as “compact working state” or “review only”.
For a proposal-only request, do not apply changes or run implementation gates;
describe the proposed validation instead.
For a general maintenance request, cover consistency, compaction and learning;
state the intended scope briefly. Inspect recent changes and unresolved
reviews first, then follow dependencies and claims across the repository.
Do not equate this pass with a fresh proof of every semantic claim.

Distinguish an observed fact, a recorded decision, a proposal and an
unverified historical claim. Compare status against actual files, commits
and check results. Do not infer that a commit was pushed, that a merged
change passed CI, or that an old successful check validates a changed tree.
Conflicting instructions or unclear authority are not resolved by silently
rewriting policy. Keep paused work paused.

## Reconcile the repository

Trace important claims to their implementation and validation:

- Code organization, imports, library boundaries, default targets and gates.
- Generated artifacts, their pinned inputs and regeneration instructions.
- README and user-facing guarantees versus actual theorem/test coverage.
- Intended design versus current capabilities, limitations and working plans.
- Document links, commands, names and authoritative ownership of each fact.
- Recorded Git/CI state versus the current refs, worktrees and run results.

Fix clear maintenance drift within the requested scope. Record substantial
semantic bugs, architectural choices or new feature work as follow-ups with
evidence and a concrete next action; do not implement them under the banner
of cleanup. Never make documentation agree by weakening a requirement or
silently overstating coverage. Use existing checks before adding new ones.

## Compact working state

Inventory `.agents/` explicitly, including hidden files. Map useful content
to its topic and owning document before moving files; consolidate first,
rather than relocating an accumulated archive. Follow AGENTS for organization.
Treat skills and machine-consumed data as maintained artifacts, not disposable
notes. Check consumers before moving data; a move without a navigation benefit
need not be part of a document refactor.

- Keep current status short: active scope, verified checkpoint, open
  obligations, exact validation evidence and the next concrete step.
- Rewrite superseded decisions in place, retaining the current reason,
  important uncertainty and revisit trigger. Do not discard a still-valid
  constraint merely because it is old or verbose.
- Preserve unresolved review findings, failed experiments that constrain
  future choices, paused work and recovery instructions. Carry their useful
  content into a retained file before removing a redundant source.
  Keep reviewed revisions, reviewer independence limits and later resolutions
  distinct. Historical recovery paths must be labeled as such, not live links.
- Promote durable artifact knowledge to its existing owner in `docs/` or
  beside code. Keep public documentation independent of `.agents/` links.
- Remove completed notes/reviews only after preserving their useful content
  and confirming their historical version is recoverable in Git. Do not
  delete uncommitted material on the assumption that history contains it.
  Repair live references to removed files and verify the resulting inventory.

Compaction preserves meaning, not every sentence. Retain enough evidence
identity to distinguish local checks, remote CI, partial coverage and
resource failures without relying on ignored logs or session transcripts.
Do not relabel an archived or timed-out experiment as completed work.

## Learn and improve

Use recent diffs, review findings, failures and available user corrections
as evidence. Prefer the smallest lasting improvement:

| Learning | Destination |
|---|---|
| Mechanically detectable regression | Existing test or validation script |
| Stable cross-cutting repository rule | Concise update to `AGENTS.md` |
| Lean-specific implementation trap | `docs/lean-pitfalls.md` |
| Cross-cutting choice and reason | `.agents/decisions.md` |
| Detailed topic choice and revisit condition | Its working note |
| Current obligation or future work | Status or roadmap |
| Artifact behavior, guarantee or usage | Owning public document or code |
| A demonstrated weakness in this procedure | This skill |

Do not create an ever-growing lessons journal or copy rules between these
owners. A single incident may justify a regression test without justifying
a universal policy. Keep useful uncertainty instead of inventing a lesson.

Change this skill only when experience or the user supports the change.
Explain the evidence and expected improvement in the diff/review, remove
obsolete guidance, and test changed behavior with a realistic scenario.
Self-improvement is optional per run, never an endless completion condition.

## Validate and hand off

Review the diff for lost obligations, changed claims and accidental scope
expansion. Run relevant checks plus the review and publication gates required
by `AGENTS.md`; record actual exit results and anything not run. After
compaction, verify links and that the resume entry points still explain all
open work. When editing this skill, also validate its metadata and behavior.

An invocation is not blanket permission to publish, delete branches or
worktrees, remove backups, rewrite history, change pins or resume campaigns.
Apply the current user authorization and repository policy to those actions.
Do not clean unknown or concurrent work merely to obtain a clean status.

Stop when scoped maintenance and required validation/review are complete, or
when a material decision needs the user. Report changes, check results,
remaining risks and follow-ups. Say what was checked rather than claiming
unqualified whole-repository consistency.
