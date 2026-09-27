# Repository stewardship

Locally completed requested maintenance, 2026-09-26, after ordering commit
`29ddf22fc5dbfb3dc77d7a7a57fbcaa5ab04db2e`. Retain this note until publication
and compact its completed evidence at the next maintenance checkpoint.

## Scope and disposition

Check consistency, compact completed working state and retain evidence-backed
lessons. No semantic implementation, pin change, campaign, branch/worktree or
backup removal is part of this pass. Nano implementation and full-P4 M3 remain
paused. Root owns edits; Luna inventories working notes and Sol audits public
claims/current paths, then independently reviews root's changes.

- Correct AGENTS descriptions of runtime support, generated output and checked
  module reachability to match the implemented organization.
- Shorten Status to current validation, open obligations and the next proof step.
  Mark old Nano checkpoint paths/commands historical without rewriting the
  evidence or weakening unresolved contracts; reconcile Roadmap's paused state.
- Remove completed `code-organization.md` after retaining its outcomes in
  AGENTS/Decisions and review/publication evidence here. Its complete original
  is recoverable at `29ddf22:.agents/notes/code-organization.md`.
- Replace the completed prior stewardship report with this checkpoint. The
  original is recoverable at `6111eb7:.agents/notes/repository-stewardship.md`:
  independent `compact_full_p4`/`compact_state` cross-reviews resolved ownership,
  provenance and runtime wording findings; no semantic audit was claimed.
  Its durable constraints already live in AGENTS, Decisions, topic notes and
  the skill. Preserve coverage's inherited determinism bookkeeping limitation,
  field-update evidence, all paused-topic reviews, the checked census and archive
  recovery instructions. No skill change is justified by this pass.

## Completed refactor evidence

`ad1ac3310e034494fa05bdbcdac395b5053860de` implements four concrete libraries,
Tools executable roots, subsystem-owned Lean tests, colocated oracle suites,
shared pinned-probe plumbing, checked library layers/reachability and existing
compiler/proof responsibility splits. Only the trivial Smoke check and proven
infrastructure duplicates were removed; semantic regressions, distinguishing
mutations, axiom audits and both independent Nano computations remain.

Independent read-only AI-agent reviews against `5687b0d`:
Sol `organize_lean_tests` reviewed checker/Tools/proof/tactic work;
Sol `enforce_library_layers` reviewed compiler/proof and final state-certificate
moves; Astra `review_oracle_refactor` reviewed plumbing, provenance, keyed cache,
relocations and consolidation. Each excluded its own implementation. No findings
remain; exact scoped hashes and original review limits are at `29ddf22` above.
All 49 generated files and 26 mapped payloads stayed byte-identical. Eight pinned
upstream capture checks passed. No full-P4 campaign was run or claimed.
The initial gate exposed a changed logical corpus ID; source lookup now resolves
stable evidence IDs separately from physical paths, preserving completion data.
The settled full gate passed (session 65742, exit 0, no skips), followed by
[exact-head CI 36280484313](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36280484313).

Ordering commit `29ddf22` preserved Lake values/membership, 131 aggregate imports,
ignore patterns, Nix package/system membership and upstream OCaml order. Sol
`enforce_library_layers` independently reviewed Sol `organize_lean_tests`'s work
and root's final comment/spacing changes; no outstanding findings. Six-file
diff SHA-256 against `ad1ac33`:
`076e98772b44d06f65c57a47605179039504f24d760a7d777195bb489d19d9e4`.
Author comparison/Nix checks and root's full gate passed (session 61425,
exit 0, no skips). Import-order behavior is supported by that full gate, not
membership comparison alone. Exact-head CI 36281893597 is still running.

## Current pass review and validation

Read-only inventory (Luna `maintenance_inventory`) found no missing local
Markdown targets; old logical oracle IDs are intentional. Public claim/path
review (Sol `enforce_library_layers`) confirmed current certification/corpus
counts and the four AGENTS corrections. These audits did not recapture upstream
observations, run proofs or certify the entire repository's semantics.

Independent read-only review: Sol `enforce_library_layers`, against `29ddf22`,
found no lost obligation or substantive error. Seven-path diff SHA-256:
`23bb8de44fdfe2a75e4e62af31f7c7bc4a17bcdc56d33f93498d3b95b360986d`.
The reviewer checked historical recovery and absence of the removed note, scope
and review limits, retained Nano WIP constraints and all changed Markdown links.
A minor attribution suggestion was applied afterward: CI 36276724234 validates
the combined `f6d1b05` checkpoint, not two independently checked commit heads.
The review is by an AI agent and does not claim fresh semantic validation.

Root's link/anchor check passed for 107 local links across 36 Markdown files;
tracked census/completion/coverage data, Lake config and lockfile are unchanged.
The deleted note was verified in committed history and absent from the resulting
17-topic-note inventory. Full local gate `nix develop -c bash scripts/check.sh`
passed with actual exit 0 (session 41273, no skips); log
`.artifacts/tend-repo-gate.log`. Only review/checkpoint metadata and prose wrapping
changed afterward; text and staged whitespace checks were rerun. Exact-head
publication CI remains required for the resulting maintenance revision.
