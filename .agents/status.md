# Status

Current state only. Updated 2026-09-26.

## Scope

M1/M2 and M3A are closed. Broader M3 is incomplete and paused. The bounded
Nano field-update consumer and repeatable certification milestone are complete.
The user approved the README, terminology note and Related Work, then requested
a whole-repository review, refinement, cleanup and commits. That checkpoint is
active; no new semantics coverage or example-library refactor is included.

The approved later refactor remains separate: rename the consumer library to
`ExampleProofs`, with its case and colocated tests in
`ExampleProofs/NanoP4FieldUpdate/`; remove it from default library builds while
retaining it explicitly in the full gate and enforce library/consumer boundaries.

## Completed implementation baseline

- Main is `395022a` before this documentation/review checkpoint. The field-update
  certificate implementation is `a249f2c`; the timeout follow-up is `395022a`.
- `NanoP4Proofs/FieldUpdate/Certificate.lean` composes representation coverage,
  actual initialization, generated forward refinement and handwritten finite
  reference realization on the scalar source domain. The example transfers
  distinct-name update commutation, not arbitrary assignment reordering.
- Colocated mutation tests reject wrong generated behavior, wrong quotation
  identity and a wrong scalar representation at the intended boundaries.
  This is selected artifact sensitivity, not general generator mutation coverage.
- Local full gate passed without skips for both commits. The first remote run
  exceeded the baseline proof subprocess's 60-second limit. Separate runtime
  (60 s) and proof (300 s) deadlines fixed that harness issue without changing
  Lean heartbeat budgets or theorem obligations. Remote run `36261314804`
  passed at `395022a`; no timeout repair remains open.
- Generated AL certificates remain 18 of 153 Nano definitions in one direction.
  Full-P4 production generation and general reverse certificates remain incomplete.

## Current review checkpoint

- README states the certifying-compiler goal, current partial coverage and the
  rationale for following P4-SpecTec and certifying reusable language models.
  `docs/related-work.md` replaces the historical prior-art comparison with
  primary-source comparisons and explicit implications for developers and users.
  The approved title and filename are "Related Work" and `related-work.md`.
  `.agents/notes/compiler-certification.md` retains the discussion reference.
- Independent documentation reviews have no unresolved findings:
  `.agents/reviews/readme-terminology.md` and `.agents/reviews/related-work.md`.
- Root's repository review found two fail-open tooling paths: text checking
  silently passed missing tracked files and split unusual filenames; upstream
  rebuilding ignored Dune failure and could accept old binaries. Both have
  scoped fixes and regression tests, with no semantic implementation changes.
- Text checking retains its shell entry point, uses NUL-delimited Git paths,
  checks UTF-8, includes Python/YAML, and fails on read/enumeration errors.
  Eleven regression tests passed. Upstream building preserves Dune's exit
  status and diagnostics with explicit root/targets; five stubbed regressions
  passed. The real pinned upstream build passed in `.#upstream`, session 93110.
- Corrected stale AL/IL, CI caching and state-carrier descriptions. Existing
  proof boundaries, pins and generated artifacts are unchanged. The expected
  four-file upstream JSON export patch is preserved.
- Final integrated `nix develop --command scripts/check.sh` passed with exit 0
  and no skips, session 36520; log: `.artifacts/repository-review-gate.log`.
  Both 78-program differential legs, 48 output contexts and all 342 quotations
  match; the certificate baseline and mutants passed their intended checks.
  All 16 new tooling regressions passed. Shell syntax, staged whitespace and
  13 public-document local links also passed. Independent tooling and final
  documentation reviews have no unresolved correctness findings.
- Commit inspection is pending. No push is requested. Documentation and tooling
  fixes will be separate logical commits with active-session coauthor trailers.

## Archived, not completed

One primary worktree and only local/remote main remain. The roughly 7 MB local
Git bundle preserves retired committed experiments; old ignored artifacts were
intentionally discarded. Recovery instructions: `.agents/notes/archive.md`.

Production aggregate `925fdbf`, source integration `1b2ac70`, still fails the
second full-P4 casting proof at the unchanged 4M heartbeat limit. Archiving is
not completion or integration. Frozen corpus `c4a8858` stopped after shards
0–44 with 180 attempts, 338 AL matches and eleven oversized-artifact failures.
Those are partial historical totals. Raw campaign artifacts were discarded;
any new run needs fresh scope and evidence, not an exact-resume claim.

## Workflow and next step

Direct commits to main are approved for normal work; feature branches are
optional and PRs require an explicit request. Independent review, a full local
gate before pushing and checking remote CI after a push remain required.

Finish validation and local commits for this review, then hand off. Do not
resume broader M3 or the separate example-library refactor in this checkpoint.
