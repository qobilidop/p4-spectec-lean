# Independent effect-interpreter review

Reviewed 2026-09-25: `a81265df153989398ac74a99eb39995cb509fe89`
against `9bc0861`, in the isolated fresh-state worktree. This review covers
the new effect interface, evaluator generalization, tactic adjustments and
AL-level tests. It does not independently re-review the reviewer-authored
earlier StateEval foundation, or claim stateful generation/refinement.

## Verdict

No outstanding findings in this checkpoint. The low-priority
regression-test weakness below was fixed and independently rechecked. The implementation is suitable
for integration subject to the separate byte-text reconciliation and full
gate; neither was run here.

## Finding

- **Resolved, low — negative-premise assertions did not distinguish inversion from
  ordinary invocation.** `P4SpecTecTest/StateInterp.lean:25` gives both
  function alternatives the same fresh-return expression; the cases at
  lines 46–48 and assertions at lines 73–75 therefore would still pass
  if `eval_if_not_hold_prem` invoked its relation without `Effects.notHold`.
  A failing relation would select the fallback and a succeeding relation
  the first clause, but both yield the same value/counter. Use distinct
  first-clause/fallback results, while preserving the allocation, to
  protect the interpreter wiring. The current implementation at
  `P4SpecTec/Interp/InterpAl/Interp.lean:926` correctly performs inversion;
  this is a test-sensitivity issue, not a discovered semantic defect.
  Root's follow-up changes only the test: `negativeFunction` gives the
  first and fallback clauses distinct `first:`/`fallback:` tags, retaining
  allocation in both. Direct `lake env lean P4SpecTecTest/StateInterp.lean`
  passed (exit 0). As an independent non-writing mutation check, the test
  was streamed through `sed` replacing `IfNotHoldPr` with `IfHoldPr` into
  `lake env lean --stdin` (under `bash -o pipefail`). It failed exactly
  the two tagged assertions (exit 1), confirming that losing inversion is
  now detected. No interpreter source was mutated.

## Semantic checks

- `Effects.lean:48` validates type/value arity before allocation, and
  delegates non-fresh operations to the existing checked dispatcher.
  Its value construction agrees with pinned `interface/builtin/fresh.ml`.
  Allocation precedes output checking, so a rejected output retains the
  advanced counter. Session state is explicit at both public entry points;
  `init` constructs tables only.
- `Effects.lean:69` selects the state-retaining carrier operations.
  All effectful recursive evaluator functions use the same carrier;
  pure context, matching and value operations are lifted rather than
  independently reimplemented. Function/relation extern callbacks share
  that carrier. No new implicit counter reset or pure fabricated ID exists.
- Relation rule prefixes remain inside each complete path attempt
  (`Interp.lean:1020`); sequential failure retries with updated state.
  This matches `interp-al/interp.ml`'s `invoke_defined_rel` and
  `backtrack.ml:46`. Negation matches upstream `eval_if_not_hold_prem`:
  success becomes mismatch, mismatch succeeds, hard error remains hard,
  without counter rollback. Explicit sequential/cache-free scope matters:
  deterministic checking may execute extra allocating alternatives.
- Stateful tracing evaluates into a local `result` at the supplied state
  (`Effects.lean:75`), then logs and returns that result. No second run or
  reset is present. The audited `traceStateRun` equation preserves the
  complete result, including errors, mismatch and divergence. This equation
  is not itself a formal theorem about physical logging/execution counts.
- Higher-order defined wrappers retain local lookup and share the session.
  The documented raw-builtin-alias boundary is pre-existing: both upstream
  and this port dispatch a looked-up builtin using the invocation's local
  identifier, rather than restoring a distinct original identifier.
  No broader callback-completeness claim follows from the wrapper fixture.
- The pure instance remains default, with identity helper lifting and
  the original pure choice/negation. The new reduction equations are
  kernel-checked; their exact axiom guards pass. `fuelArgument?` reads
  instantiated binder types and the first explicit Nat argument, instead
  of assuming the first application argument is fuel. Both users retain
  ordinary checked proof application. No theorem statement, fragment
  classification, axiom allowance or proof-error recovery was weakened.
  General `Effects` instances are not assumed lawful by a new theorem.

## Independent validation

All commands used `nix develop /Users/qobilidop/my/work/p4-spectec-lean
--command ...`, with explicit fresh-state worktree cwd. Upstream source
was read from the original checkout at
`8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3`.

- `lake build --wfail P4SpecTec P4SpecTecTest.StateInterp`: exit 0,
  67 jobs (existing artifacts reused where current).
- `lake env lean P4SpecTecTest/StateInterp.lean`: exit 0, directly
  re-elaborating the AL fixtures and fuel-binder test.
- Additional `lake env lean --stdin` sensitivity checks: exit 0.
  Tested a traced two-allocation computation from seed 41 returning
  `FRESH__42` and counter 43; success does not run an allocating fallback;
  an allocating hard error stops before fallback; two rejected alternatives
  retain counter 43; an undefined extern preserves a preceding allocation;
  divergence does not select fallback. The first scratch attempt had two
  test-only elaboration mistakes (missing result-type annotation and a
  broken projection line); the corrected complete invocation passed.
- `git diff --check 9bc0861 a81265df153989398ac74a99eb39995cb509fe89`:
  exit 0. Read the full relevant interpreter/tactic changes and exact
  upstream allocation, failure, negation, invocation and path-order code.

Not independently run: full gate, Nano proof rebuild, corpus comparison,
remote CI, whole-AL upstream effect oracle. The author's recorded Nano
proof/build evidence is separate, not relabeled as reviewer execution.
Durable whole-AL upstream effect fixtures and generated stateful code,
Prop encodings and refinement proofs remain future validation obligations.
Human-facing documentation reconciliation is an integration obligation;
the isolated worktree's older status/design are not evidence that these
later stages are complete.

## Byte-text integration review

Reviewed the primary `m3b-effect-integration` worktree applying the effect
checkpoint and test correction (`a81265d`, `21ee889`) over byte-text base
`e1c5555`. No integration findings.

Compared the merged interpreter against the isolated effect checkpoint:
its remaining differences are the byte-text port's literal, index, slice,
and update helpers, including negative text-slice rejection. Effectful
expression/premise control flow retains those helpers and byte length/
concatenation rather than reintroducing character operations. Compared
Effects, StateInterp and the tactic against `21ee889`: the production
adaptation is `ByteText.ofString` at fresh-value construction, plus a
corrected dispatcher classification docstring; the tactic is unchanged.
Fresh IDs contain only ASCII prefix, sign and decimal digits, so UTF-8
encoding preserves the upstream bytes exactly. Test observations use
checked UTF-8 decoding, not replacement decoding.

Independent checks in the primary worktree's default Nix shell:

- Direct `lake env lean P4SpecTecTest/StateInterp.lean`: exit 0.
- Additional `lake env lean --stdin` interaction guards: exit 0. A fresh
  allocation followed by invalid `text_to_int` preserves the counter and
  returns hard error without running fallback; wrong text-builtin arity
  retries at the updated counter. A raw `[255, 0, 169]` TextE survives
  stateful evaluation unchanged, and indexing retains raw byte `[255]`
  without affecting the allocation count. An earlier draft had a scratch
  syntax error; the corrected complete invocation passed.
- Inspected updated human-facing design boundaries: interpreter effects
  are delivered, stateful generation/refinement remains future work,
  and sequential/cache-free execution is explicitly distinguished from
  deterministic checking. No widened proof claim was introduced.

The integrating author's focused build and forthcoming full gate are
separate evidence; this narrow review did not run the full gate or remote
CI. Only this report was edited by the reviewer.
