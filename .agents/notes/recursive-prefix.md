# Recursive rejected-prefix proof prototype

2026-09-25. Isolated branch `m3b-recursive-prefix`, based on `f07ddad`.
This is a bounded proof experiment, not stateful code generation.

## Question and result

A stateful successful rule needs evidence for the complete attempts that
failed before it. Those attempts can call the same recursive SCC. The
`partial_correctness` principle exposes approximating recursive functions,
whereas the generated relation must name the final executable definitions
inside its `RejectedPrefix`. A success-only recursive hypothesis cannot
transport a mismatch equation and its consumed state between them.

`P4SpecTecTest/RecursivePrefix.lean` demonstrates a stronger motive:

```text
walk motive:
  finalWalk n s = some outcomeAndState
  AND every successful outcome satisfies structural Walk

reject motive:
  finalReject n s = some outcomeAndState
  AND the outcome is not a success
```

`walk` and `reject` form a genuine mutual SCC. `walk` first tries `reject`;
`reject` allocates and recursively calls `walk` before mismatching. The
successful fallback allocates and recursively walks again. In the proof,
the rejecting approximant's mismatch is transported to the final `reject`
definition at exactly the same post-state, then used to construct the
`RejectedPrefix` witness. `Walk` remains an inductive with base/step rules,
literal fresh-name production, and a recursive `Walk` premise. It is not
defined by an equality to `walk`.

The operational realization component is auxiliary. It quantifies over
every terminating outcome pair, not only successes. Its composition uses
the existing `StateRefines Eq`, `stateRefinesBind`, and
`stateRefinesOrElse`; the tiny `realization` and `transport` lemmas connect
that calculus with equations. No new library API was needed. All named
theorems and both recursive definitions have exact axiom guards; the
structural soundness proof uses only `propext`, `Classical.choice`, and
`Quot.sound`. There is no `sorry`, `native_decide`, or weakened failure
relation.

## Computational evidence

Seven Lean `#guard` checks observe both outcome and final state:

| Run from zero | Outcome | Final counter |
|---|---|---:|
| `reject 0` | mismatch | 1 |
| `reject 1` | mismatch | 2 |
| `reject 2` | mismatch | 5 |
| `walk 0` | `[]` | 1 |
| `walk 1` | `[FRESH__2]` | 4 |
| `walk 2` | `[FRESH__5, FRESH__8]` | 10 |

The seventh check starts `walk 1` at signed maximum, crossing the signed
wrap in a rejected recursive prefix before producing its result.

The concrete mutual fixture has successful and mismatching executions;
it does not claim a reachable hard-error branch. The realization motive
and transport lemma nevertheless retain both error tags without
restriction; `hardErrorTransport` separately audits that case.

## Validation and remaining scope

All commands run in the isolated prototype worktree, through
`nix develop /Users/qobilidop/my/work/p4-spectec-lean --command`.
It has its own `.lake`; neither the primary nor frozen interpreter
worktree was modified or used as a shared build directory.

- `lake build --wfail P4SpecTec.Refine.StateCalc`: exit 0.
- `lake build --wfail P4SpecTecTest.RecursivePrefix`: exit 0, including
  the mutually recursive proof and seven execution guards.
- `scripts/check-imports.sh P4SpecTec P4SpecTecTest`: exit 0.
- `scripts/check-text.sh`: exit 0.
- `git diff --check`: exit 0.

Initial development builds failed on a reserved binder name and on
over-eager reduction of state binds; those were corrected. No failed
build is counted as validation. This note records focused checks only;
no full gate, upstream differential oracle, or remote CI was run here.

The prototype uses a specialized no-success invariant for `reject` so the
only successful rule is the fallback. A general generator must instead
produce the appropriate constructor when any earlier attempt succeeds,
and preserve all accumulated mismatch witnesses when it advances.
General ordered-iteration structural evidence, strict positivity, mutual
relation groups, theorem generation, and tactic automation remain separate
obligations. This experiment establishes that recursive rejected-prefix
transport is feasible without making the successful relation tautological;
it does not establish the complete stateful generator design.
