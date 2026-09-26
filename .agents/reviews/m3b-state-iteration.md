# Independent stateful iteration integration review

2026-09-25. Root reviewed proof checkpoints `381dd6a`, `25ad4f2` and
`815b671`, integrated with executable checkpoint `e0d7219` on
`m3b-generator-integration`. The reviewer did not author these changes.

No correctness findings remain in the bounded nonrecursive scope.
Production stateful proof selection deliberately remains disabled.

## Semantic boundary

Successful positive relation calls retain inductive relation evidence,
not only equations about their executable runs. Ordered list iteration
uses `StateChain` with linked intermediate states. Its helper predicates
are mutual inductives indexed by captured values, so recursive predicate
parameters are not hidden inside closures. Empty lists preserve state;
optional all-absent branches likewise preserve their incoming state.
Mixed optional inputs remain executable hard errors rather than successful
structural cases.

Rejected complete attempts retain exact mismatch equations and post-state.
They are closed over their original inputs before selected-path
substitutions, preventing capture by equally named local temporaries.
Iterator captures use private binders; inherited substitutions are frozen
before entering the iterator scope and shadowed names are excluded.

The expanded actual-emission tests cover empty and nonempty lists, nested
lists with an empty inner list, joint lists and multiple outputs, optional
absence/presence/mixed cases, computed captures from pattern-bound inputs,
and shadowed iterator names. A direct constructor example checks that
positive premises remain structural. The generic tactic extension restores
the full elaborator state on false, exception and unfinished success;
the rollback fixture checks goal identities and assignments.

## Verification

Commands ran in the pinned Nix shell with the integration worktree as
explicit working directory:

- `lake build --wfail P4SpecTec P4SpecTecTest.StateProps
  P4SpecTecTest.StateCodegen P4SpecTecTest.Updates
  P4SpecTecTest.Text.Main`: exit 0, 78 jobs.
- `lake env lean P4SpecTecTest/StateProps.lean`: exit 0, direct independent
  re-elaboration of the actual generated declarations and axiom audits.

Read the full structural emitter, state tactic, new state lemmas, generic
tactic extension and emitted-code fixtures. Recursive SCC automation,
generated AL refinement, full-P4 elaboration and the integrated full gate
are outside this focused review. Their absence is not a passed milestone.
