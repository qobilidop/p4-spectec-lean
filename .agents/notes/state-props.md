# Stateful structural rules: bounded generator checkpoint

This working checkpoint adds an isolated `Codegen.StateProps` backend and
`state_run_sound` tactic. Production selection remains disabled. It depends
on the shared executable `Mode`/`Attempt`/statement API snapshot; those files
belong to the executable-codegen workstream, not this patch.

## What is represented

Every constructor has the original notation-order relation arguments and
explicit initial/final `FreshState` indices. Its `RejectedPrefix` records
every earlier **complete** attempt, including input matching, shared
premises, path premises and output evaluation. A selected attempt starts
at that prefix's exact consumed post-state. No prefix is omitted for an
`else` attempt.

Positive relation premises carry the callee's structural relation with
linked states. Function and extern calls carry exact successful paired
outcomes. Negative premises carry exact mismatch outcomes and post-state;
they do not use negation of an inductive relation. Pure operations retain
their existing structural facts and consume no state.

`Refine.StateRules` adds audited exact choice/negation/lifting equations
and an ordered `StateChain` whose steps are structural relation evidence.
The initial tactic handles nonrecursive relations, including iteration. Its
symbolic execution keeps failed-attempt equations for the prefix witness.
It does not establish a refinement theorem against the interpreter.

## Evidence

In the isolated `p4-spectec-lean-state-props` worktree, with the original
repository's flake:

```
nix develop /Users/qobilidop/my/work/p4-spectec-lean --command \
  lake build --wfail P4SpecTecTest.StateProps
```

Exit 0 (63 jobs). The fixture constructs real AL definitions and elaborates
the actual emitted executable, inductive and run-soundness declarations.
Every emitted theorem is immediately audited. It covers allocation,
shared-prefix retry, a positive structural call, an impossible rule and
negation retaining the failing callee's state. Six execution guards check
names, mismatch tags and final counters, including a nonzero session seed.
A direct constructor example checks that the positive premise accepts
structural evidence rather than requiring its executable graph.

The additional `lake build --wfail P4SpecTec P4SpecTecTest.StateProps`
finished with exit 0 (72 jobs). `scripts/check-text.sh` and
`git diff --check` both returned 0.

Early focused builds exposed harness `run_elab`/command-monad mismatch,
negation's arbitrary `Unit` result normalization, and the lack of a `BEq`
instance for a test result; all were fixed before the successful check.
No full gate or remote CI is claimed for this isolated checkpoint.

## Independent-review capture fix

The root reviewer found that selected-path text substitutions could capture
an earlier attempt's bound temporary. In the reproducer, both paths used
`tmp_0` at different types; matching `some n` in the selected path rewrote
the earlier `ByteText` allocator binder. The emitted inductive failed to
elaborate, correctly preventing its run-soundness theorem from passing.

Earlier attempts are now closed over explicit input lambdas. Only their
application arguments receive selected-path substitutions; their bodies
remain untouched. Prefix constructor-binder relevance also uses only those
free application arguments and state indices, excluding body-local names.
The original reproducer is a compiled fixture, alongside a two-input rule
whose selected aliases reverse the earlier local names. Both branches and
their consumed states have runtime guards. The focused test build again
returns 0 (63 jobs); no iteration support was mixed into this fix.

## Ordered and optional iteration checkpoint

`relInductives` emits a mutual block's declarations: the original relation
and auxiliary step predicates whose indices carry captured values. Ordered
premises use `StateChain`; optional premises have absent/present constructors
with exact state flow. Captures receive private names before inherited
substitutions enter the iterator scope, preserving outer computed values
even when iterator binders shadow their source variables. Nested helpers
receive distinct names. This keeps recursive predicate parameters closed.

The tactic derives the chain from the actual successful `mapM` observation
and recursively proves each structural step. A transactional extension to
the existing constructor search restores both assignments and goals after
failure, unfinished work or exceptions; an exact-axiom regression checks it.
Optional joint matching normalizes product equalities before substitution.

The actual-emission fixtures cover empty/populated list maps, captured
inputs, joint list inputs with multiple collected outputs, a computed
capture from a pattern-bound value shadowed by the inner iterator, nested
lists including an empty inner list, and optional all-absent/all-present/
mixed-presence behavior after an allocation. Every emitted soundness theorem
is audited; execution guards check both outputs and final states.

After these additions, `lake build --wfail P4SpecTec P4SpecTecTest.StateProps`
exited 0 (72 jobs) in the pinned Nix shell; `scripts/check-text.sh` and
`git diff --check` also exited 0. No full gate or remote CI is claimed.

## Remaining boundaries

- Recursive SCC automation needs the stronger **all-outcome** realization
  motives demonstrated by the separate recursive-prefix fixture. The
  initial tactic supplies no recursive induction hypotheses.
- Stateful determinism and interpreter refinement are not generated.
- Production selection and the census must not treat this bounded
  generator as full-P4 structural support.
- Shared executable callback SCC monotonicity and optional-expression
  correctness findings remain the executable author's obligations.
