# Explicit state: retained implementation and remaining integration

Compacted 2026-09-26 from the 2026-09-25 checkpoints. This is working
knowledge for paused work, not a new semantic review. [Review evidence](review.md) retains
the individual reviewers, checked revisions and limits. Full original notes
and reports are recoverable at Git commit `968ad65` under their former paths.

## Current boundary

The explicit-state carrier, shared interpreter, bounded executable emitter,
structural fixtures and bounded function-refinement emitter are retained.
Production `Codegen/Emit.lean` still rejects `freshState`; production
`Validate` does not count the bounded `StateValidate` fixtures as full-P4
coverage. The main census has no production full-P4 stateful certificates.
Broader M3 is paused. Historical worktree instructions and publication TODOs
are checkpoint history, not instructions to revive removed worktrees.

The broader production aggregate `925fdbf` (source integration `1b2ac70`)
is retired, not completed: its second full-P4 casting proof still failed at
the unchanged 4M heartbeat limit. See [archive recovery](../archive.md);
do not infer that its recursive automation landed from an old note's
“completed checkpoint” wording.

## Why this state and mode

At upstream `8c8e0c6f`, `interface/builtin/fresh.ml` validates type/value
arity, formats `FRESH__` plus the old signed counter, increments, then
registers the value. `Builtin.Call.Make` owns the counter. Its reset has no
observed caller in the pinned library/runner: rebuilding interpreter tables
does not reset a session. Choice retries only mismatch, preserving consumed
IDs; hard errors stop. Negation preserves effects too. IDs affect substitution,
generated declarations, equality and printing, so alpha-normalizing names
would change observations.

`FreshState = BitVec 63` models the pinned 64-bit OCaml signed range
`[-2^62, 2^62 - 1]`, including wrap to `-4611686018427387904` after the
maximum. `StateEval = ExceptT Fail (StateT FreshState Option)` returns
`FreshState → Option (Except Fail α × FreshState)`; placing state above
failure would erase failed-attempt counters. Only session boundaries supply
or reset state. Pure lifting preserves it; divergence remains outer `none`.
The 32-bit OCaml boundary is not covered. Nor is the cache side-effect
detector's inability to notice a complete `2^63` allocation cycle.

Decision (2026-09-25): select uniform `freshState` from a `BuiltinDecD`
named `fresh_typeId`, never from the library name, a user function or a
direct-call closure. Retain pure mode otherwise. Callbacks and externs can
hide effects, so mixed signatures need an additional sound effect analysis.
All function/relation/table/callback/extern ABIs share the selected carrier;
internal calls use `ExceptT.mk (callee args)` without choosing a state.
Confidence is high in the uniform direction; revisit the proof API and
scaling when production integration resumes.

The original snapshot audit (raw SHA-256
`803d798c13ae102e6aa970f65dfd2313d9d9b4094cae745049d3418c1af11953`)
found 1,055 non-extern callables/865 SCCs. Fresh reverse reachability had
262 nodes/139 SCCs (23 recursive); additionally seeding all seven higher-order
definitions gave 275/152 (29 recursive). Five extern declarations were
outside that SCC graph. Direct fresh callers were `fresh_typeIds`,
`TypeArgument_ok`, `DirectApplicationStmt_inst`. The closed-spec 28 global
callback actuals were fresh-free, but exported callbacks need not be.
These measurements justify conservative mode selection, not a proved effect
analysis. The scanner followed complete output/premise expression trees and
else paths, matching `callsOfDef`; full reconstruction is in the old
`fresh-identifiers.md` at the recovery commit.

## Shared interpreter and oracle

One `Interp.Effects` evaluator specializes to `Eval` or `StateEval`.
Ctx/type/value helpers remain pure and are lifted. Old pure entry points
and unannotated call syntax survive. State entry points return post-state
on success and either failure; `init` only builds tables. Tracing observes
the actual result once at the supplied state, with an audited preservation
equation. The refinement tactic locates fuel by its explicit `Nat` binder.
Shared premises rerun per complete attempt; `DebugPr` evaluates even though
printing is omitted. Arity rejection precedes allocation; output rejection
after allocation keeps the counter.

Execution is sequential/cache-free. Upstream deterministic checking can
evaluate extra alternatives and consume IDs; registration, hooks and
backtraces are outside this profile. Guard-disabled callback tests do not
establish guarded higher-order fidelity. Raw builtin/extern aliases dispatch
under their local copied name upstream. Generated global `DefA` sites reject
them; a defined wrapper calling the original global name is supported.

`test/state/run.py` links the actual pinned AL functor and checks repository
root, indexed gitlink and checkout HEAD. `check-state-oracle` reads the
fixture at runtime and requires its exact ordered cases/revision/scopes.
Its 15 observations separate ten complete AL/session cases from five direct
builtin cases. AL cases cover allocation, retry, hard-failure stopping,
three distinctly tagged negations, shared-prefix retry, wrapper callback,
extern-triggered retry and session continuation. Primitive cases cover
valid allocation, both arity errors and signed wrap. Seeds and post-states
are observed, not inferred. AL uses `cache=false, det=false, guard=false`.
The public upstream API collapses internal Err/Unmatch, so complete-AL
comparison checks observable success/failure and exact state; primitive
BuiltinError requires Lean `.unmatch`. Lean-only fixtures separately check
both failure tags, output validation and zero fuel. Ten corrupt-fixture
mutations must fail. This oracle is not a generated-code/full-P4 oracle.

## Executable and structural translation constraints

`Attempt.ofRelation` flattens complete input/shared/path/output attempts in
source order, else last. Hoisting a shared fresh premise across retries would
return `FRESH__0`/state 1 instead of `FRESH__1`/state 2. Callback lookup is
lexical before global/extern; dependency collection includes global DefA
edges and excludes local binders, including callback-only SCCs and extern
requirements. Preserve nested DefP signatures; reject rank polymorphism and
function-valued data, including direct ExpP FuncT, results, aliases and
containers, until faithful codecs exist. Type-body validation is a finite
scan, not unbounded recursive alias expansion.

Optional expressions and premises distinguish all-present/all-absent/mixed
inputs; mixed presence is a hard error even for a pure expression body.
`Stmt.optM` retains binder/body/result structure needed by structural proofs.
Recursive callback consumers use audited least-fixed-point monotonicity
lemmas, never an assumed extern/callback contract. Discovery computes a finite
closure only for recursive definitions. Other higher-order recursive shapes
must prove monotonicity or fail elaboration.

`StateProps` constructors retain notation-order arguments and initial/final
states. `RejectedPrefix` records each earlier complete mismatch and exact
post-state; the selected path starts there, including else. Positive relation
premises stay inductive; functions/externs have exact successful equations;
negative premises have mismatch equations, not negation of an inductive.
`StateChain` links ordered structural premises. Auxiliary mutual step
predicates carry captured values as indices, with closed predicate parameters.
Optional absent branches preserve state; mixed branches have no successful
constructor. Earlier attempts close over input lambdas before selected-path
substitution; private iterator captures prevent temporary-name capture.
Constructor search restores assignments and goals on failure/exception or
unfinished success. These are bounded nonrecursive generated fixtures.

The recursive `RecursivePrefix` and `StateRules` experiments prove feasibility
of stronger partial-correctness motives: every terminating approximant
outcome/post-state is realized by the final function, with a separate
structural success component. This transports recursive mismatches into
`RejectedPrefix`, then converts ordered `MapSteps` into `StateChain` using
structural induction hypotheses. The successful relation is not its run
graph. Their rejecting attempts have proved no-success invariants; a general
translator must also construct earlier successful cases. Neither fixture
has a reachable hard-error branch; a separate transport theorem audits that
tag. Capturing a constructor-local value inside a `StateChain` predicate
lambda fails Lean's nested-inductive check; make that value an input/index.

## Refinement and next obligations

`StateRefines` relates every terminating interpreter outcome at arbitrary
fuel and initial state, retaining failure tags and exact final state.
`StateEvals` permits skipped interpreter-only steps only when they succeed
and preserve state. Bind/choice/negation/map calculus retains failed-prefix
effects. Exhaustion supplies no one-way obligation; it is not success.

`Refine.StateInterp` reaches real fresh dispatch and `invoke_func`; hypotheses
disable guards, select the builtin via `Holds`, and require an empty local
function table for that corollary. Lower lookup permits a matching local
declaration under the actual fresh name, not arbitrary aliases. The emitted
allocator fixture invokes `Funcs.builtinDecl`, parses/elaborates its output
and proves about that very definition. A resetting wrapper is rejected at
fuel 3, seed 5 even with an indiscriminate value relation (post-states 6/1).

`StateValidate`/`state_refine_al` are separate bounded eligibility/automation.
They reuse pure normalization and callee `.state_refines` contracts; missing
contracts fail loudly. The admitted slice is scalar first-order functions,
variable patterns, direct fresh calls, nested calls, if/debug premises,
ordered fallback and literal Nat division (including division-by-zero hard
failure). Recursion, relations, higher-order/type arguments, compound types,
nonvariable patterns, general arithmetic and other builtins remain excluded.
All emitted theorems are audited; no success-only weakening is permitted.

Before widening: independently check each proof probe, propagate exclusions
through callees and recursive groups (comment-only output is not coverage),
integrate production structural/run-soundness selection without dropping
rung 1, add recursive fuel induction and modular group hypotheses, and keep
stateful determinism separate. Seven tiny refinement fixtures took 37 seconds;
measure normalization and quoted-list membership proof cost before scaling.
Large recursive callback groups also need measurement. Full-P4 regeneration,
elaboration, upstream coverage and general reverse certificates remain open.
