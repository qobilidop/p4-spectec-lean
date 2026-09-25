# M2 plan: rung 3 and the lemma library on Nano-P4

Working note, 2026-09-25. What M2 delivers (design section 10), in the
order it is built, with the shape decided for each part and why. Each
phase ends in a checkpoint commit on `m2-nano-p4` with the gate green;
decisions made here are copied into `.agents/decisions.md` at the
checkpoint that makes them.

## Findings that fix the shape (experiments, 2026-09-25)

- `partial_fixpoint` accepts a body in `ExceptT Fail Option` (failure as
  data, `none` as divergence) once two monotonicity lemmas are added:
  one for `ExceptT.mk` and one for our `orElse` (which retries only on
  `Unmatch`, as `choose_sequential` does). `List.mapM`, `match`, `do`
  binds and `if` are covered by Lean's own lemmas.
- `partial_correctness` is derived only when the definition's type is
  syntactically `Option _`. So a generated definition has type
  `Option (Except Fail T)`, its body is `ExceptT.run (do ...)` in the
  monad, and recursive calls are lifted with `ExceptT.mk`. For a mutual
  group Lean derives `f.mutual_partial_correctness` with one motive per
  member and one hypothesis per member (each with the induction
  hypotheses for every member).
- The kernel rejects a relation occurring under `∃`, `∧` or `∨` inside its
  own constructors ("nested inductive datatypes parameters cannot contain
  local variables"). It accepts it under `∀` and `→`. So in the `Prop`
  encoding every temporary is a constructor-bound variable with an
  equation hypothesis, and an iterated premise that mentions a relation
  is `∀ i (h : i < xs.length), ... → R ...` with its temporaries
  ∀-bound and their equations as implication hypotheses; a relation-free
  iterated premise is the executable equation itself.
- Nano-P4 has no `else` rule group, two `else` clauses (functions only),
  no `IfNotHoldPr`, 30 `IfHoldPr`, 52 iterated premises, none nested; 18
  rule groups take a case pattern as input, all irrefutable or guarded by
  a `matches` premise the binding pass inserted.

## Phase A: fuel-free executable encoding

- `P4SpecTec/Prelude/Eval.lean` (ours): `Fail := err | unmatch` (upstream's
  `Err` and `Unmatch` without the failure traces), `Eval := ExceptT Fail
  Option`, `check` (`if` premise: `unmatch`), `orElse` (sequential
  choice, `err` not retried), `notHold` (for `does not hold`),
  `liftOpt` (a pattern shape that does not match: `err`, upstream's
  `assign_exp` error), `diverge`, and the monotonicity lemmas. The run
  lemmas for symbolic execution (`run_bind`, `run_pure`, `run_check`,
  `orElse_ok`, `mapM_ok`) live here too.
- Codegen: no `fuel` binder; every definition `: Option (Except Fail T)`
  with body `ExceptT.run (do ...)`; calls hoisted as
  `let x ← ExceptT.mk (f args)`; a recursive group ends with
  `partial_fixpoint` on every member; `<|>` becomes `Eval.orElse`;
  `Iter.check` becomes `Eval.check`; the `Externs` fields have the same
  `Option (Except Fail T)` shape. Failure kinds mirror the interpreter:
  `if` false and builtin failure are `unmatch`; index and slice out of
  bounds, division by zero, `^`, a failed downcast and a pattern shape
  mismatch are `err` (upstream errors or aborts there; none is reachable
  on guarded AL). A `does not hold` premise keeps `err` distinct, closing
  the M1 deviation.
- Non-recursive definitions are plain `def`s (no `partial_fixpoint`).
- Rung 2 must still give 78 of 78; `nano-p4-run` drops its fuel logic.

## Phase B: `Prop` encoding, run-soundness, inversion, axiom audit

- Per relation `R` with inputs `I` and outputs `O`: `inductive R : I → O →
  Prop`, one constructor per rule path named by `Names.ruleName`, in
  spec order; hypotheses are the premises in order, in the same A-normal
  form as the run function so that symbolic execution of `R.run` yields
  exactly them: a hoisted call is `f args = some (.ok tmp)`, an `if` is
  `e = true`, a `let` with a refutable pattern is `v = pattern`, a rule
  premise is `R' ins outs`, a `holds` premise is `R' args`, an iterated
  premise as in the findings above. A `let` with an irrefutable pattern
  is substituted (zeta), as `do` does. An `else` group (none in Nano-P4)
  carries no negation of the other groups: deviation, listed.
- Per recursion group: one generated theorem by
  `mutual_partial_correctness` with motive `True` for functions and
  `fun i r => ∀ o, r = .ok o → R i o` for relations, then per relation
  `theorem R.run_sound : R.run i = some (.ok o) → R i o` as a corollary.
  The proof of each group hypothesis is a generic tactic `run_sound`
  (`P4SpecTec/Tactic/RunSound.lean`): symbolic execution by the run
  lemmas, a case split per `orElse`, then the constructor for that path
  applied to the hypotheses in order.
- Per relation, inversion `theorem R.inv : R i o → (rule₁ hyps) ∨ …` by
  `cases`; every theorem followed by `#guard_msgs in #print axioms`
  (expected set: `propext`, `Classical.choice`, `Quot.sound`, from
  `partial_fixpoint`; recorded exactly as observed).
- Proof-checking time enters `docs/timing-nano-p4.md`.

## Phase C: the AL interpreter in Lean

- `P4SpecTec/Interp/InterpAl/{Backtrack,Ctx,Interp}.lean` mirror
  `interp/interp-al/{backtrack,ctx,interp}.ml` function by function in
  order (`nondet.ml` is the deterministic-mode checker; not ported, the
  design ports sequential mode). The monad is `Eval`; the context is a
  pure structure (no hash tables, caches, hooks or traces); `Value.Match`
  (`runtime/value/match.ml`), `Type.Subst` and `Typ.Make.iterate` are
  ported beside them at their paths. `partial_fixpoint` throughout,
  with the `Option (Except Fail _)` typing for `partial_correctness`.
- Rung 2, second leg: `nano-p4-interp` runs `Program_ok` through the
  Lean interpreter on the AL export for every corpus program and the
  harness compares with upstream's verdicts and outputs. This tests the
  trusted port directly (design section 5, rung 2).

## Phase D: value relations, lemma library, refinement theorems

- Per generated type `τ`, a relation `τ.Rel : value → τ → Prop`, generated
  with the type (mirrors CakeML's `INT`, `LIST_TYPE`): the value is the
  `toValue` image, so `τ.Rel v x := v = toValue x` up to notes, stated
  as an inductive per variant case for inversion.
- Per definition `d`, the reified term `⌜d⌝` (the AL definition as Lean
  data, decoded from the export at generation time and printed) and the
  theorem `d.refines : interp ⌜d⌝ vs = some (.ok r) → ∃ x, Rel r x ∧ d xs
  = some (.ok x)`, by a syntax-directed tactic over the interpreter's
  unfolding with the per-construct lemma library
  (`P4SpecTec/Tactic/Refine.lean`, `Interp/Lemmas.lean`).
- Whatever the tactic cannot close is reported, not `sorry`ed: the
  generator emits the theorem only for definitions in its supported
  fragment and lists the rest.

## Phase E: determinism attempt, timing, records, review

- `theorem R.det : R i o → R i o' → o = o'` attempted per relation by
  a tactic (`cases` both derivations, `simp_all`, induction hypotheses
  for recursive premises); relations where it fails are reported as
  findings in `docs/`, the theorem is not emitted for them.
- Timing table regenerated with proof-checking time; design sections
  4.1, 5.1, 5.3, 6 updated; decisions updated; status rewritten;
  independent review filed under `.agents/reviews/`; merge to `main`.
