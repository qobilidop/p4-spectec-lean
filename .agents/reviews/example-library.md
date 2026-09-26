# Example library separation

2026-09-26. Independent read-only review by `/root/doc_guides_review` of the
refactor after `af78615`; boundary implementation by `/root/example_boundaries`,
with root responsible for the move, integration, documentation and final gate.

## Scope and findings

- All ten moved proof/test files match the originals after only namespace,
  path and library-name substitutions. Root independently repeated this
  comparison. The aggregate root additionally documents its example role.
  Theorems, source domains, axiom sets, mutation boundaries and timeout budgets
  are unchanged.
- `ExampleProofs` is registered but excluded from default targets. The full
  gate explicitly builds it, checks root imports and runs colocated mutation
  contract and replay tests. Reusable support remains under `P4SpecTec.Refine`.
- The new checker uses the pinned Lean import parser, not a regex or the
  dependency CLI that discards parser diagnostics. It rejects direct and
  indirect local dependencies from reusable libraries to examples/tests,
  including disconnected reusable modules, malformed headers, missing inputs,
  configuration overrides and subprocess failures.
- Review found one configuration gap: a package-level `srcDir` override could
  make Lake build sources outside the checker's inventory. The writer verified
  this against pinned Lake, rejected the override and added a regression.
  No unresolved correctness findings remain.
- README, Certification, Related Work, build instructions and active handoff
  references use the new names. Design retains the intended one-way dependency
  policy; Performance and timing data are unchanged. Old names in historical
  review reports describe the code/commands reviewed then, not active paths.

## Evidence

- Reviewer independently ran all 27 policy/parser tests with `--lean`: exit 0,
  session 8797. Actual repository boundary check: exit 0, session 65592.
- Root's default build: exit 0, 139 jobs, session 93460. Explicit ExampleProofs
  build: exit 0, 91 jobs, session 64241. The default build log contains no
  example build tasks.
- Colocated runner contract tests: nine passed. All 33 local README/docs links
  and Markdown anchors resolve. Shell syntax and text/whitespace checks pass.
- Root's full gate passed with exit 0 and no skips, session 54960, including
  the certificate baseline and all mutation boundaries under the new namespace.
  Log: `.artifacts/example-refactor-gate.log`. Independent review did not
  perform a separate Lean build or mutation replay. No semantic
  implementation change, new timing measurement, pin update or push is claimed.
