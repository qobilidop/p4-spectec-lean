# Stateful integration plan

2026-09-25. Based on an independent GPT-6 Astra architecture audit after
the reviewed fresh-state foundation. Generator support remains planned;
the shared interpreter is implemented, preserving Nano's pure API and proofs.

Step 1 is now implemented and independently reviewed: `Refine/StateCalc`,
StateEval monotonicity/execution equations and `P4SpecTecTest/StateCalc`.
Focused builds, exact axiom guards and the recursive structural-rule
fixture pass; the integrated full gate is recorded in status. Step 2's
shared interpreter is independently reviewed and undergoing integration;
durable complete-AL upstream observations are still being implemented.

## Decision and scope

Select a uniform stateful execution mode structurally when the spec declares
the `fresh_typeId` builtin. Do not select by library name or by a direct-call
effect closure: callbacks and externs can hide effects. All callables,
callback return types and extern fields in that mode return:

```lean
FreshState → Option (Except Fail Result × FreshState)
```

Call sites lift `ExceptT.mk (f args)` without choosing/resetting the state.
Only an execution/session boundary supplies state. Retain the pure mode
for specs without freshness. Confidence: high for uniform mode versus
mixed signatures; medium for the exact proof/API implementation. Revisit
if the prototype cannot preserve pure reduction behavior or if meaningful
state-indexed rule proofs require a materially different representation.

## Corrections required before enabling effects

- `Codegen/Rels.lean:groupTerm` currently shares match/premises outside
  path alternatives. Upstream `interp.ml:1362–1410` and our interpreter
  rerun that prefix for every attempted path. Stateful generation must
  flatten complete attempts in the same order. Regression: shared fresh
  allocation, first path mismatch, second path returns the allocation;
  from zero the result is `FRESH__1`, final state 2, not `FRESH__0`/1.
- Higher-order codegen currently emits pure arrows and globally qualifies
  callback calls. Mode-aware callback signatures and local-before-global
  DefP resolution are separate obligations. Test named and forwarded
  callbacks; uniform state alone does not fix them.
- Iterated premises need an ordered chain of states, not independent
  pointwise witnesses. Negative premises retain the mismatching call's
  final state. Failed earlier alternatives can affect the selected path.
- `DebugPr` currently skips compiling its expression. Evaluate it even
  when printing is omitted, preserving its effects and failures.
- Dependency collection must include global `DefA` references and exclude
  lexically shadowed local callbacks; otherwise SCC/file placement and
  extern-instance requirements are incomplete.
- A rejected attempt can call the same recursive SCC. The existing
  structural fixture's rejected prefix is nonrecursive; prototype stronger
  all-terminating-outcome realization motives before translating those
  failure equations into witnesses over final, not approximate, calls.

## One interpreter, two specializations

Parameterize the evaluator, Config and Extern over a small transparent
effect interface: pure lifting, sequential choice, negation, builtin
dispatch (including allocation), and observation/tracing. Do not copy
the interpreter. Keep pure Ctx/value/type helpers and lift them.
Preserve old pure entry points by specialization, with definitional
compatibility or explicit lemmas adequate for the existing Nano tactics.
Observation must execute at the supplied state once, never reset or run
the computation again merely to inspect its outcome.

## Meaningful state-indexed relations

Keep named successful path constructors for
`R inputs initialState outputs finalState`. A path-k constructor carries:

1. A finite `RejectedPrefix` witness for complete attempts before k,
   each returning `some (.error .unmatch, nextState)` in order.
2. Structural premises for the selected path starting at that post-state.
3. State-indexed positive relation premises, function-call equations and
   the selected path's final state.

This is not a definition of R as its run graph. Computational failure
witnesses extend the existing negative-premise deviation while successful
rule semantics remain structural. A wholly structural all-outcome Exec
judgment is larger and is not silently claimed. Negative calls explicitly
record input/post-state; iteration records intermediate states in order.

The run-soundness tactic must recognize paired outcomes, retain equations
for rejected alternatives (it currently discards them), and use paired
partial-correctness motives/corollaries. These are adaptations, not an
obstacle to the Option-returning recursion carrier: an ignored scratch
allocator probe passed `partial_fixpoint` with two monotonicity lemmas and
only `propext`, `Classical.choice`, `Quot.sound`.

## Refinement contract

For every initial state and terminating interpreter outcome, generated
execution must have a related outcome and exactly the same final state.
This includes success, mismatch and hard error. Literal IDs are observable;
alpha-normalization and success-only state equality are insufficient.
Port bind, choice, negation and ordered-map calculus to that contract.
Interpreter-only computations skipped by generated code must both succeed
and preserve state; inability to fail alone no longer justifies skipping.

## Implementation order

1. State equations/monotonicity and a state-sensitive refinement calculus;
   tiny recursive proof fixture with a rejected prefix.
2. Shared interpreter specialization and fresh builtin validation, session
   continuation and pinned upstream differential fixtures.
3. Generator mode, signatures, callbacks, repeated-prefix fix; executable
   failure/negation/iteration/recursive/extern fixtures.
4. State-indexed Prop and run-soundness, including rejected-prefix and
   ordered-iteration evidence.
5. Generated stateful refinement with exact all-outcome state agreement.
6. Full-P4 regeneration/elaboration, measured coverage, full gate and
   independent review. Keep any remaining rejection explicit.

The executable and proof generators can be split after freezing a shared
mode/complete-attempt/statement interface. Production state mode must remain
an explicit rejection until structural Prop and run-soundness are supported;
never silently omit the existing rung-1 guarantees. Pure determinism emission
cannot be reused unchanged for state-indexed relations.

Separate higher-order interpreter boundaries remain: `Match.sub_` rejects
`FuncT`, type-parameter freshening uses deterministic names, and direct builtin
aliases dispatch by the local identifier. Guard-disabled callback fixtures
do not establish guarded full-P4 fidelity. These need separate scoped fixes
and oracle evidence.
