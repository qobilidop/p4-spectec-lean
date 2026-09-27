import P4SpecTec.Refine.Realize

/-!
Discriminating eventual-realization fixtures. These exercise independent fuel
bounds, ordered failures and exhaustion; they do not certify an AL definition.
-/

namespace P4SpecTecTest.Realize

open P4SpecTec.Prelude P4SpecTec.Refine

def delayed (bound : Nat) (r : Except Fail α) (fuel : Nat) : Eval α :=
  ExceptT.mk (if bound ≤ fuel then some r else none)

theorem delayedRuns (bound : Nat) (r : Except Fail α) :
    EventuallyRuns (delayed bound r) r := by
  exact ⟨bound, fun _ h => ite_eq_left h⟩

/-- info: 'P4SpecTecTest.Realize.delayedRuns'
does not depend on any axioms -/
#guard_msgs in #print axioms delayedRuns

-- Independent witnesses at bounds 2 and 9 must be raised to a common bound.
theorem sharedFuel :
    EventuallyRuns (fun fuel =>
      delayed 2 (.ok 4) fuel >>= fun n => delayed 9 (.ok (n + 3)) fuel) (.ok 7) :=
  (delayedRuns 2 (.ok 4)).bindOk (delayedRuns 9 (.ok 7))

/-- info: 'P4SpecTecTest.Realize.sharedFuel'
depends on axioms: [propext] -/
#guard_msgs in #print axioms sharedFuel

theorem fixedOverhead :
    EventuallyRuns (fun fuel => delayed 9 (.ok 7) (fuel - 5)) (.ok 7) :=
  (delayedRuns 9 (.ok 7)).offset 5

/-- info: 'P4SpecTecTest.Realize.fixedOverhead'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fixedOverhead

theorem failedPrefix :
    EventuallyRuns (fun fuel => Eval.orElse
      (delayed 11 (.error .unmatch) fuel) (delayed 3 (.ok 7) fuel)) (.ok 7) :=
  (delayedRuns 11 (.error .unmatch)).orElseUnmatch (delayedRuns 3 (.ok 7))

/-- info: 'P4SpecTecTest.Realize.failedPrefix'
depends on axioms: [propext] -/
#guard_msgs in #print axioms failedPrefix

theorem hardErrorStops :
    EventuallyRuns (fun fuel => Eval.orElse
      (delayed 11 (.error .err) fuel) (delayed 3 (.ok 7) fuel)) (.error .err) :=
  (delayedRuns 11 (.error .err)).orElseError (delayed 3 (.ok 7))

/-- info: 'P4SpecTecTest.Realize.hardErrorStops'
does not depend on any axioms -/
#guard_msgs in #print axioms hardErrorStops

theorem bindErrorStops :
    EventuallyRuns (fun fuel =>
      (delayed 4 (.error .err) fuel : Eval Nat) >>= fun _ =>
        (Eval.diverge : Eval Bool)) (.error .err) :=
  (delayedRuns 4 (.error .err)).bindError (fun _ _ => Eval.diverge)

/-- info: 'P4SpecTecTest.Realize.bindErrorStops'
does not depend on any axioms -/
#guard_msgs in #print axioms bindErrorStops

theorem exhaustionIsNotMismatch :
    ¬ EventuallyRuns (fun _ => Eval.orElse
      (Eval.diverge : Eval Nat) (pure 7)) (.ok 7) := by
  intro h
  obtain ⟨fuel, hfuel⟩ := h.witness
  cases hfuel

/-- info: 'P4SpecTecTest.Realize.exhaustionIsNotMismatch'
does not depend on any axioms -/
#guard_msgs in #print axioms exhaustionIsNotMismatch

theorem exhaustionCannotRealize :
    ¬ Realizes Eq (fun _ => (Eval.diverge : Eval Nat)) (pure 7) := by
  intro h
  obtain ⟨fuel, r, hr, _⟩ := h.witness rfl
  cases hr

/-- info: 'P4SpecTecTest.Realize.exhaustionCannotRealize'
depends on axioms: [propext] -/
#guard_msgs in #print axioms exhaustionCannotRealize

theorem failureKindsCannotChange :
    ¬ Realizes (fun (_ _ : Nat) => True)
      (fun _ => throw .unmatch) (throw .err) := by
  intro h
  obtain ⟨fuel, r, hr, hrel⟩ := h.witness rfl
  cases hr
  cases hrel

/-- info: 'P4SpecTecTest.Realize.failureKindsCannotChange'
depends on axioms: [propext] -/
#guard_msgs in #print axioms failureKindsCannotChange

theorem hardErrorRealizes :
    Realizes Eq (fun _ => (throw .err : Eval Nat)) (throw .err) :=
  Realizes.error Eq .err

/-- info: 'P4SpecTecTest.Realize.hardErrorRealizes'
depends on axioms: [propext] -/
#guard_msgs in #print axioms hardErrorRealizes

theorem negatedMismatch :
    EventuallyRuns (fun fuel => Eval.notHold
      (delayed 5 (.error .unmatch) fuel : Eval Nat)) (.ok ()) :=
  (delayedRuns 5 (.error .unmatch)).notHold

/-- info: 'P4SpecTecTest.Realize.negatedMismatch'
does not depend on any axioms -/
#guard_msgs in #print axioms negatedMismatch

-- A single finite execution is insufficient to assume fuel stability.
def onlyZero (fuel : Nat) : Eval Nat :=
  ExceptT.mk (if fuel = 0 then some (.ok 7) else none)

example : (onlyZero 0).run = some (.ok 7) := rfl

theorem finiteNeedNotBeEventual : ¬ EventuallyRuns onlyZero (.ok 7) := by
  rintro ⟨bound, hbound⟩
  have h := hbound (bound + 1) (by omega)
  simp [onlyZero] at h

/-- info: 'P4SpecTecTest.Realize.finiteNeedNotBeEventual'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms finiteNeedNotBeEventual

-- The hard error at input 1 must precede and suppress divergence at input 2.
def step : Nat → Eval Nat
  | 0 => pure 7
  | 1 => throw .err
  | _ => Eval.diverge

def referenceStep (fuel n : Nat) : Eval Nat :=
  if n + 2 ≤ fuel then step n else Eval.diverge

theorem stepRealizes (n : Nat) :
    Realizes Eq (fun fuel => referenceStep fuel n) (step n) := by
  intro q hq
  refine ⟨q, ⟨n + 2, fun fuel hfuel => ?_⟩, ?_⟩
  · simpa only [referenceStep, ite_eq_left hfuel] using hq
  · cases q with
    | ok _ => rfl
    | error _ => rfl

/-- info: 'P4SpecTecTest.Realize.stepRealizes'
depends on axioms: [propext] -/
#guard_msgs in #print axioms stepRealizes

theorem orderedTraversal :
    Realizes (List.Forall₂ Eq)
      (fun fuel => [0, 1, 2].mapM (referenceStep fuel)) ([0, 1, 2].mapM step) := by
  apply Realizes.mapM (P := Eq) (.cons rfl (.cons rfl (.cons rfl .nil)))
  intro a b hab
  subst b
  exact stepRealizes a

/-- info: 'P4SpecTecTest.Realize.orderedTraversal'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms orderedTraversal

theorem orderedTraversalError :
    ∃ fuel, (([0, 1, 2].mapM (referenceStep fuel)).run) = some (.error .err) := by
  obtain ⟨fuel, r, hr, hrel⟩ := orderedTraversal.witness (q := .error .err) (by rfl)
  cases r with
  | ok _ => cases hrel
  | error e =>
    cases hrel
    exact ⟨fuel, hr⟩

/-- info: 'P4SpecTecTest.Realize.orderedTraversalError'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms orderedTraversalError

-- Both generic rules retain the existing delayed failure/divergence distinction.
theorem negatedStep (n : Nat) :
    Realizes (fun _ _ => True)
      (fun fuel => Eval.notHold (referenceStep fuel n)) (Eval.notHold (step n)) :=
  (stepRealizes n).notHold

/-- info: 'P4SpecTecTest.Realize.negatedStep'
depends on axioms: [propext] -/
#guard_msgs in #print axioms negatedStep

theorem optionalTraversal (input : Option Nat) :
    Realizes (Option.Rel Eq)
      (fun fuel => input.mapM (referenceStep fuel)) (input.mapM step) := by
  apply Realizes.optionMapM (P := Eq)
  · cases input with
    | none => exact .none
    | some _ => exact .some rfl
  · intro a b hab
    subst b
    exact stepRealizes a

/-- info: 'P4SpecTecTest.Realize.optionalTraversal'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms optionalTraversal

-- An absent optional body is skipped even at fuel zero; a present hard error
-- is retained, and insufficient fuel is never mistaken for an absent option.
example : ((none : Option Nat).mapM (referenceStep 0)).run = some (.ok none) := rfl
example : ((some 1).mapM (referenceStep 3)).run = some (.error .err) := rfl
example : ((some 1).mapM (referenceStep 0)).run = none := rfl

end P4SpecTecTest.Realize
