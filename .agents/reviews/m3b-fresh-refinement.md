# Independent fresh-refinement boundary review

2026-09-25. Read-only review of the uncommitted
`P4SpecTec/Refine/StateInterp.lean` and
`P4SpecTecTest/StateRefinement.lean` on `m3b-state-refinement`, base
`7d9d35658370cfc614efda0e3e8ab2d3adbbe7a6`. Reviewed by the executable
codegen agent, independently of the root author's implementation. Only
this report was written; no implementation, fixture, branch or commit
was changed.

## Findings

No high, medium or low correctness findings in the stated bounded scope.

The statement reaches actual `invoke_func`, `invoke_func_body` and
`invoke_builtin_func`, rather than proving only that the allocator refines
itself. Fuel exhaustion at each dispatch layer is covered by the existing
one-way divergence boundary. For a defined result, `StateRefines`
requires exactly the same post-state, and `ResRel` preserves both failure
kinds. No successful-result-only weakening is introduced.

The hypotheses are adequate and explicit: disabled guards, the selected
builtin declaration and empty local function bindings for the `Holds`
corollary. The lower lookup theorem allows either cursor only when lookup
actually selects the stated declaration under `fresh_typeId`; it does not
assert that a differently named builtin callback alias has the same
meaning. The global table obligation is a real hash-map lookup, and the
concrete fixture establishes it. Arbitrary tracing configurations are
handled by the existing stateful trace implementation without rerunning
the computation or resetting its state.

Fresh dispatch's value relation is appropriate: runtime `Value.Make.text`
and typed `ByteText` produce the same semantic bytes through `Rel`.
The theorem quantifies over all initial `FreshState` values, including
signed wrap. The separate malformed-arity equation covers both nonempty
type-argument lists and nonempty value-argument lists and preserves the
initial state on mismatch.

The composition fixtures use actual interpreter dispatch followed by
both kinds of failure, ordered retry and negation. They instantiate the
existing exact-state calculus; they do not claim that arbitrary AL
premises have already been related to generated terms. `resetRejected`
is nonvacuous: interpreter fuel 3 produces an actual fresh result at
state 5, and a value-insensitive relation still cannot equate final
states 6 and 1. Every advertised theorem has an exact axiom audit;
the new modules contain neither `sorry` nor `native_decide`.

## Verification

All commands used
`nix develop /Users/qobilidop/my/work/p4-spectec-lean --command ...`
with explicit primary-repository workdir.

- `lake build --wfail P4SpecTec.Refine.StateInterp
  P4SpecTecTest.StateRefinement`: exit 0, 44 jobs.
- `lake env lean
  /Users/qobilidop/my/work/p4-spectec-lean/P4SpecTec/Refine/StateInterp.lean`:
  exit 0, direct re-elaboration including exact axiom audits.
- `lake env lean
  /Users/qobilidop/my/work/p4-spectec-lean/P4SpecTecTest/StateRefinement.lean`:
  exit 0, direct re-elaboration including the reset counterexample.

Inspected supporting `StateCalc`, `Calc.Holds`/`ResRel`, `Value.Rel`, the
actual shared interpreter dispatch and guard definitions, and
`Interp/Effects.lean`. The author's full-gate report was read but the full
gate was not independently rerun by this reviewer. Remote CI, generated
stateful refinement, full-P4 compilation and additional upstream oracle
runs are outside this review. The notes accurately retain those limits.
