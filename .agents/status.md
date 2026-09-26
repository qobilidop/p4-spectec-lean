# Status

Current state only. Updated 2026-09-26.

## Scope

The approved repo-local `tend-repo` skill is implemented and locally validated.
This packages an on-demand maintenance workflow; it does not invoke a
whole-repository cleanup or resume feature work. Publication is pending.

## Skill checkpoint

- `.agents/skills/tend-repo/SKILL.md` is instruction-only and refers to
  `AGENTS.md` for policy. Navigation and the stewardship decision are updated.
- The bundled `quick_validate.py` passed on the final skill (session 82926),
  using temporary Python/PyYAML from the locked nixpkgs input. No dependency
  or pin changed. Text hygiene and staged whitespace checks passed.
- Independent review and a read-only behavioral trial passed. The trial led
  to explicit proposal-only validation guidance; broader maintenance proposals
  were not applied. Evidence and limitations: `.agents/reviews/tend-repo.md`.
- Full `nix develop --command scripts/check.sh` passed with exit 0, no skips,
  session 20758; log `.artifacts/tend-repo-gate.log`. The census still contains
  1,689 definitions. Code, generated artifacts and proof budgets are unchanged.
- Checkpoint the skill locally as "Add on-demand repository stewardship".
  Hold its push while the refactor CI runs: another main push would cancel
  that run. Remote CI has not validated this skill checkpoint yet.

The approved library/example separation is complete after the README and
documentation review. Broader M3 remains incomplete and paused.
The bounded Nano field-update certificate is complete; this refactor changes
its organization and build boundary, not its semantics or proof coverage.

## Current checkpoint

- Rename `NanoP4Proofs/FieldUpdate/` to
  `ExampleProofs/NanoP4FieldUpdate/`, with all eight proof modules and the
  colocated mutation runner/tests. Imports, namespaces, axiom expectations
  and scratch-probe extraction anchors use the new names.
- `ExampleProofs` is a registered library outside default targets. The full
  gate explicitly builds it, checks its root imports and runs its tests.
  Reusable proof infrastructure remains in `P4SpecTec.Refine`.
- A Lean-parser-backed import-boundary checker and regression tests enforce
  that reusable libraries cannot reach examples or test-only modules,
  including through local bridge modules; default build classification is
  checked as well.
- README, Certification, Related Work, AGENTS and live working notes now
  reference the new location. Design keeps its intended architectural policy;
  Performance and the historical timing measurements are unchanged.
- Explicit `lake build --wfail ExampleProofs` passed (91 jobs), session 64241.
  Default `lake build --wfail` passed (139 jobs), session 93460.
  The colocated mutation runner's nine contract tests passed.
- Full `nix develop --command scripts/check.sh` passed with exit 0 and no
  skips, session 54960; log `.artifacts/example-refactor-gate.log`. All 27
  boundary policy/parser tests passed; the certificate baseline and all
  mutations passed at their intended boundaries after the rename.
- Independent review found and fixed a package-source-directory checker gap;
  no unresolved findings remain. Report: `.agents/reviews/example-library.md`.
  All 33 public-document local links/anchors, shell syntax and text/whitespace
  checks pass. Old source paths are absent. The ten proof/test files were
  mechanically verified unchanged beyond name/path substitutions.
- The refactor was integrated and pushed to `main` at `aa24ab7` under the
  confirmed no-PR workflow. Remote CI run `36268161537` is still in progress;
  the finished local branch remains until that run passes.

## Retained baseline

- The published baseline is `aa24ab7`, including documentation/review commits
  `4f6c504`, `6134bb2` and `af78615`. The remaining local
  `docs/repository-review` branch points to that integrated commit; the skill
  checkpoint follows it on local main.
- The concise Design describes the destination. Certification owns current
  capabilities, guarantees and limitations; Performance owns measurements;
  README gives a short status. Keep these responsibilities when updating docs.
- Field-update certification connects the actual generated helper to the
  initialized quoted AL reference in both directions on a scalar source
  domain and transfers distinct-name commutation. It does not justify
  arbitrary P4 assignment reordering.
- Generated AL certificates remain 18 of 153 Nano definitions in one
  direction. Full-P4 production generation and general reverse certificates
  remain incomplete.
- The previous documentation checkpoint's full gate passed without skips,
  session 47549. The field-update baseline's timeout repair passed remote CI
  at `395022a`, run `36261314804`; no timeout repair remains open.
- The expected four-file upstream JSON export patch remains applied.
  No generated source, pin, theorem obligation or timeout budget is changed.

## Archived, not completed

One worktree remains. The small local Git bundle preserves retired committed
experiments; ignored artifacts were discarded. See `.agents/notes/archive.md`.
The archived full-P4 casting experiment still failed its second proof at the
unchanged 4M heartbeat limit; partial corpus totals are not completion evidence.
No broader campaign resumes as part of this task.

## Workflow and next step

Confirm refactor CI run `36268161537` and remove its finished local branch
after success. Publish the locally validated skill checkpoint under the
checked-in no-PR workflow and verify its remote CI. An actual `tend-repo`
maintenance pass is separate work. Do not resume broader M3.
