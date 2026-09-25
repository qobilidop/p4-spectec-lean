# State-sensitive calculus and recursive fixture

2026-09-25. Independent read-only review by OpenAI Codex (GPT-6 Astra)
of the new diff against `1b34d71`. The reviewer authored the earlier
foundation, not this calculus; that earlier work was excluded. No findings.

StateRefines uses the same initial state and requires exact final-state
equality for every terminating success, mismatch or hard error. ResRel
preserves the distinct failure kinds. StateEvals requires success and
unchanged state for terminating interpreter-only steps; divergence remains
deliberately unconstrained by one-way partial correctness. Bind, choice,
negation and map rules retain consumed state. RejectedPrefix links actual
mismatch outcomes and states; MapSteps records ordered iteration states.

The recursive Ids fixture is genuinely structural: named nil/cons rules,
rejected-prefix evidence, and a recursive Ids premise. Its soundness proof
uses the generated partial-correctness principle, not a definition of Ids
as the evaluator's run graph. Negative fixtures reject erased failure
states, changed failure tags and skipped allocations. Monotonicity uses
the flat Option boundary and pointwise state carrier. Exact axiom guards
pass; the recursive fixture uses only the permitted standard axioms.

Independent validation in the required Nix shell, all exit 0:

- `lake build --wfail P4SpecTec P4SpecTecTest.StateCalc` (66 jobs).
- Direct elaboration of StateCalc, StateEval and the StateCalc test.
- Import coverage, whitespace and new-file line hygiene.

This completes only the planned contracts/proof-fixture stage. It does
not establish interpreter/generator integration, generated state-indexed
relations, mutual-recursion tactics, upstream differential agreement or
stateful AL refinement. No full gate was run by the reviewer; integration
evidence belongs in primary-worktree status.

A separate GPT-6 Sol documentation review confirmed that the new design,
status and integration-note claims match the contracts and fixture. Its
wording suggestion was applied: rejected prefixes record mismatching
alternatives specifically, not hard errors (which stop choice). The
primary full gate subsequently passed, exit 0 with no skips.
