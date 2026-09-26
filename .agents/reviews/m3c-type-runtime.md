# Independent checked type-runtime review

2026-09-25. Root reviewed the bounded implementation by the type-runtime
agent, including the added checked signature pipeline. No findings remain
within the explicitly documented comparison boundary.

Read new Expand/Equiv modules and the checked Subst/Typ/Func/Ctx/Match APIs,
every changed interpreter call site, the fixtures and the oracle runner.
Compared equivalence, matching, casts and map construction with the pinned
OCaml sources. Initial findings were corrected: inner-before-iterator error
ordering; structural mixfix traversal instead of whole-shape prefiltering;
matched-branch substitution arity errors; last-binding-wins maps; exact
source/build provenance; and nested-signature exhaustion propagated through
lookup rather than silently replacing a function parameter by its result.

The checked interpreter distinguishes true mismatch, hard error and exhausted
computation. Nonempty substitution through function types remains an explicit
unsupported error. Private alpha markers do not escape a Boolean comparison,
but this does not model the separate mutable Type.Fresh counter or later
observations after it advances. OCaml physical-identity short-circuiting is
not represented. These limits are named in the design and remain M3 work.
Legacy total APIs remain available to existing proof clients; the interpreter
uses the checked path. The optional-iteration non-option success behavior is
unusual but matches the pinned upstream branch exactly.

## Independent verification

- `nix develop <type-runtime> --command lake env lean
  <type-runtime>/P4SpecTecTest/TypeRuntime.lean`: exit 0, including real
  interpreter SubE, guard and callback paths plus error/exhaustion tests.
- `nix develop <primary>#upstream --command python3
  <type-runtime>/test/type-runtime/run.py --upstream
  <primary>/upstream/p4-spectec --check`: exit 0, fourteen pinned observations.
- `nix develop <type-runtime> --command python3
  <type-runtime>/test/type-runtime/test_contract.py`: exit 0, three offline
  provenance/build-order tests with mutation subcases.

The author's 153-job focused library/test build passed; root did not rerun
that entire build during review. Full integrated gate, CI wiring, final
remote CI and whole-corpus replay remain separate obligations.
