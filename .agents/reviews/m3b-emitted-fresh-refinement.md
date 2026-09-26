# Independent emitted fresh refinement review

2026-09-25. Root independently reviewed `ae91edd`, authored by the
executable codegen agent, on the integrated executable/proof branch.
No correctness findings.

The fixture invokes `Funcs.builtinDecl`, parses and elaborates its output,
and names that emitted definition directly in the refinement target.
There is no handwritten replacement definition. The general theorem
retains all fuel, initial state, guard and lookup hypotheses from the
interpreter boundary; composition covers both failures, retry and negation.
The reset mutation wraps the actual generated function and is rejected by
an exact-state kernel counterexample, even with a trivial value relation.
Every advertised theorem has an exact axiom audit. The note correctly
limits the result to the fresh builtin rather than arbitrary generated AL.

Independent commands in the pinned Nix shell and integration worktree:

- `lake build --wfail P4SpecTecTest.StateGeneratedRefinement P4SpecTec`:
  exit 0, 75 jobs.
- `lake env lean P4SpecTecTest/StateGeneratedRefinement.lean`: exit 0,
  direct re-elaboration including the actual generator and axiom checks.

The combined full gate and remote CI are separate release obligations.
