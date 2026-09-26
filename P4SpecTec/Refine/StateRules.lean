import P4SpecTec.Refine.StateCalc

/-!
Structural ordered state premises and exact execution equations for stateful
run-soundness (not a mirror). A chain contains relation evidence, not just
the graph of a computation; its intermediate states are linked in order.
-/

namespace P4SpecTec.Refine

open P4SpecTec.Prelude

/-- An ordered list of structural premises, with one linked state transition per element. -/
inductive StateChain (P : α → FreshState → β → FreshState → Prop) :
    List α → FreshState → List β → FreshState → Prop where
  /-- An empty iteration consumes no state. -/
  | nil (s) : StateChain P [] s [] s
  /-- The next premise starts at the preceding premise's exact post-state. -/
  | cons {a as s b t bs u} : P a s b t →
      StateChain P as t bs u → StateChain P (a :: as) s (b :: bs) u

/-- Per-element soundness turns a computational trace into structural ordered evidence. -/
theorem StateChain.ofMapSteps {P : α → FreshState → β → FreshState → Prop}
    {f : α → StateEval β}
    (step : ∀ a s b t, StateEval.run (f a) s = some (.ok b, t) → P a s b t)
    {as : List α} {s : FreshState} {bs : List β} {t : FreshState}
    (h : MapSteps f as s bs t) : StateChain P as s bs t := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (step _ _ _ _ h) ih

/-- info: 'P4SpecTec.Refine.StateChain.ofMapSteps' does not depend on any axioms -/
#guard_msgs in #print axioms StateChain.ofMapSteps

/-- Pack captured values into chain indices, leaving the recursive predicate constant. -/
theorem StateChain.ofRunWithContext {P : (γ × α) → FreshState → β → FreshState → Prop}
    (context : γ) {f : α → StateEval β}
    (step : ∀ a s b t, StateEval.run (f a) s = some (.ok b, t) →
      P (context, a) s b t)
    {as : List α} {s : FreshState} {bs : List β} {t : FreshState}
    (h : StateEval.run (as.mapM f) s = some (.ok bs, t)) :
    StateChain P (as.map fun a => (context, a)) s bs t := by
  have steps := runMapMSteps h
  clear h
  induction steps with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (step _ _ _ _ h) ih

/-- info: 'P4SpecTec.Refine.StateChain.ofRunWithContext' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs in #print axioms StateChain.ofRunWithContext

/-- Ordered choice retains the exact mismatch post-state before trying its right branch. -/
theorem stateRunOrElseOk (a b : StateEval α) (s t : FreshState) (x : α) :
    StateEval.run (StateEval.orElse a b) s = some (.ok x, t) ↔
      StateEval.run a s = some (.ok x, t) ∨
        ∃ u, StateEval.run a s = some (.error .unmatch, u) ∧
          StateEval.run b u = some (.ok x, t) := by
  rw [StateEval.run_orElse]
  cases StateEval.run a s with
  | none => simp
  | some r =>
    rcases r with ⟨r, u⟩
    cases r with
    | ok y => simp
    | error e => cases e <;> simp

/-- info: 'P4SpecTec.Refine.stateRunOrElseOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stateRunOrElseOk

/-- The notation for sequential choice has the same complete-attempt equation. -/
theorem stateRunHOrElseOk (a b : StateEval α) (s t : FreshState) (x : α) :
    StateEval.run (a <|> b) s = some (.ok x, t) ↔
      StateEval.run a s = some (.ok x, t) ∨
        ∃ u, StateEval.run a s = some (.error .unmatch, u) ∧
          StateEval.run b u = some (.ok x, t) := stateRunOrElseOk a b s t x

/-- info: 'P4SpecTec.Refine.stateRunHOrElseOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stateRunHOrElseOk

/-- A successful negative premise retains its called relation's mismatch post-state. -/
theorem stateRunNotHoldOk (a : StateEval α) (s t : FreshState) (x : Unit) :
    StateEval.run (StateEval.notHold a) s = some (.ok x, t) ↔
      StateEval.run a s = some (.error .unmatch, t) := by
  cases x
  rw [StateEval.run_notHold]
  cases StateEval.run a s with
  | none => simp
  | some r =>
    rcases r with ⟨r, u⟩
    cases r with
    | ok y => simp
    | error e => cases e <;> simp

/-- info: 'P4SpecTec.Refine.stateRunNotHoldOk' depends on axioms: [propext] -/
#guard_msgs in #print axioms stateRunNotHoldOk

/-- Successful pure lifting records that no state was consumed. -/
theorem stateRunLiftOk (a : Eval α) (s t : FreshState) (x : α) :
    StateEval.run (StateEval.liftEval a) s = some (.ok x, t) ↔
      a.run = some (.ok x) ∧ s = t := by
  rw [StateEval.run_liftEval]
  cases a.run <;> simp

/-- info: 'P4SpecTec.Refine.stateRunLiftOk' depends on axioms: [propext] -/
#guard_msgs in #print axioms stateRunLiftOk

/-- Calling a generated explicit-state result preserves its caller's session. -/
theorem stateRunMk (f : FreshState → Option (Except Fail α × FreshState)) (s : FreshState) :
    StateEval.run (ExceptT.mk f) s = f s := rfl

/-- info: 'P4SpecTec.Refine.stateRunMk' does not depend on any axioms -/
#guard_msgs in #print axioms stateRunMk

end P4SpecTec.Refine
