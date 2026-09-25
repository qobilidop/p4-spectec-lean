# Ordered structural state-premise review

2026-09-25. Root-agent independent read-only review of the StateRules
fixture in `2c08752`. No findings in its stated bounded scope.

`StateChain` requires a structural premise for each element and links
successive states. `Visits.node` uses the recursive `Visits` predicate,
not merely executable `MapSteps`; its other hypothesis records exact
states consumed by the earlier rejected recursive attempt. The successful
relation is not defined as the program's run graph.

The proof's stronger partial-correctness motive transports every terminating
recursive result/poststate to the final function. It uses that realization
for the rejected-prefix witness, and separately uses the successful
structural induction hypothesis at each ordered map step. The failed
attempt's no-success lemma is explicit, not an assumed tactic shortcut.
All new theorem axiom sets are immediately audited; the soundness theorem
uses only the permitted standard axioms.

The negative captured-predicate example is meaningful: Lean rejects a
constructor-local value captured in the nested inductive parameter, while
the capture-free predicate with explicit inputs is accepted. It does not
prove that every future generated iteration layout will pass positivity.

Independent command in the state-props worktree through the pinned default
Nix shell: `lake env lean P4SpecTecTest/StateRules.lean` exited 0, including
four actual execution guards, the negative kernel diagnostic and all axiom
guards. Root inspected the executable and structural/proof definitions in
full. No source changes were required; this report is the review artifact.

No generic stateful Prop translator, proof tactic, full-P4 build or upstream
differential claim follows from this fixture. Its successful-first-attempt
and arbitrary iterated-premise cases remain general-generator obligations.

## Integrated checkpoint

The primary focused build of both recursive proof fixtures exited 0
(44 jobs); both subsequent full `scripts/check.sh` invocations exited 0
with no skipped gates. A separate GPT-6 Sol read-only review of the status
compaction and integration plan found no lost M3 obligations or exaggerated
proof claims. Its stale PR #13 CI-status finding was corrected after the
remote gate passed and the PR merged. Production state generation is still
explicitly rejected pending the structural generator and automation.
