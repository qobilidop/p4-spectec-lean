# Repository maintenance review

2026-09-26. Reviewed by root against `395022a` plus the approved README and
related-work revisions. This is a repository-wide maintenance and consistency
review with targeted semantic-boundary inspection, not a new proof of upstream
fidelity or a line-by-line re-audit of every mirrored/generated declaration.

## Scope

- Inspected the tracked layout, worktree/branch state, staged and unstaged
  changes, pins, Nix shells, Lake libraries and CI workflow.
- Traced generator planning and certificate eligibility, result/failure and
  explicit-state carriers, the refinement contract, axiom auditor, quotation
  comparison, scalar field-update certificate and mutation harness.
- Checked build/export/snapshot and differential-test entry points, fail-open
  shell patterns and proof escape-hatch searches. Existing generator/tactic
  `partial def` helpers are not generated proof axioms. No proof obligation,
  timeout budget, upstream pin or generated artifact was weakened.
- Reconciled public claims and active handoff descriptions with retained main,
  including production stateful rejection versus bounded emitter/proof fixtures.
  Historical experiment notes are not evidence of integrated full-P4 coverage.

## Fixed findings

1. The shell text checker returned success for a missing tracked file and
   split whitespace-containing filenames. It now uses a small Python checker
   behind the existing shell entry point: NUL-delimited Git enumeration,
   explicit read/UTF-8 failures and preserved Lean rules. Python and YAML
   source files are included. Eleven regression tests cover file names,
   missing/staged-deleted inputs, invalid text, read/enumeration failures,
   line limits and invocation outside the repository.
2. The upstream Dune pipeline suppressed failure with `|| true`. Cached
   binaries could make a failed rebuild appear successful. The build now
   preserves Dune's status and diagnostics and supplies an explicit root.
   Five regression tests cover stale executables after failure, missing or
   non-executable outputs and successful explicit-root invocation.
3. Documentation still referred to `lean-action`, an opam repository pin,
   IL compiler input and pre-integration state support. Updated the descriptions
   to the actual Nix/AL configuration and current bounded state fixtures.
   The reconnaissance note now distinguishes 1,055 executable emission probes
   from rejected production stateful planning and zero production refinement
   eligibility; these are not a successful full-P4 build.
4. Compacted the current status and replaced the obsolete review-waiting
   handoff. The approved example-library refactor remains a separate step.

## Independent checks

`/root/ci_timeout` independently reviewed the text checker and upstream build
fixes, ran their initial 11 and three regression tests, checked shell syntax,
and probed non-executable main/nano outputs. No correctness findings. Its
coverage suggestion led to explicit missing-nano and non-executable tests;
the final five upstream regression tests passed under root.

Documentation source reviews remain recorded in `readme-terminology.md` and
`related-work.md`. Root inspected the final modifications rather than relying
only on those earlier reviews. `/root/priorart_semantics` also reviewed the
final design/reconnaissance and environment corrections against current code,
CI and the census; no blocking findings.

## Validation and remaining boundaries

- Full `nix develop --command scripts/check.sh`: actual exit 0, session 41611,
  no skips. This included warning-failing Lean builds, test modules, generated
  source checks, oracle/differential checks, quotation comparison, mutation
  sensitivity and the full-P4 capability census.
- `nix develop .#upstream --command scripts/build-upstream.sh`: exit 0,
  session 93110. The expected export patch remained applied; pins unchanged.
- The new text checker passed all 11 tests. The final upstream harness passed
  all five tests, including the two added after independent review.
- Final integrated full gate: exit 0, no skips, session 36520; log at
  `.artifacts/repository-review-gate.log`. Staged whitespace, shell syntax and
  all 13 local Markdown links in README/docs passed. Staged changes contain
  no generated artifacts, export changes or pin updates.
  Existing macOS linker deployment-version diagnostics are toolchain warnings,
  not Lean warnings or silently skipped checks.

Known semantic exclusions remain explicit: partial Nano certification,
production stateful integration, full-P4 generation, general reverse
correspondence, extern and guarded higher-order coverage, and legacy helper
fuel behavior outside the certified fragment. The archived casting experiment
is not an integrated fix. The review does not authorize resuming broader M3.
No push or remote CI run is included in this local-commit request.
