import P4SpecTec.Tactic.IterationColumns

/-! Column relation inference follows source binding arity rather than carrier shape. -/

namespace P4SpecTecTest.Tactic.IterationColumns

open Lean Elab Tactic Meta P4SpecTec.Tactic P4SpecTec.Refine P4SpecTec.Prelude
open P4SpecTec.Lang.Il

elab "check_columns" source:term "against" generated:term "using" expected:term : tactic =>
    withMainContext do
  let source ← Term.elabTerm source none
  let generated ← Term.elabTerm generated none
  let expected ← Term.elabTerm expected none
  Term.synthesizeSyntheticMVarsNoPostponing
  let some relation ← columnTraversalRelation (← instantiateMVars source)
      (← instantiateMVars generated) | throwError "output column relation was rejected"
  unless ← isDefEq relation expected do throwError "output columns use incorrect encoders"

-- One source binding with a product carrier requires only its whole-carrier encoder.
example {α β : Type} [ToValue (α × β)] (_xs : List Nat)
    (_source : Nat → Eval (List value)) (_generated : Nat → Eval (α × β)) : True := by
  check_columns (do
    let rows ← List.mapM _source _xs
    collectColumns 1 rows) against (do
    let values ← List.mapM _generated _xs
    (pure values : Eval (List (α × β)))) using
      (fun (row : List value) (pair : α × β) => canons row = canons [toValue pair])
  trivial

-- Two source bindings instead require distinct component dictionaries, in source order.
example {α β : Type} [ToValue α] [ToValue β] (_xs : List Nat)
    (_source : Nat → Eval (List value)) (_generated : Nat → Eval (α × β)) : True := by
  check_columns (do
    let rows ← List.mapM _source _xs
    collectColumns 2 rows) against (do
    let values ← List.mapM _generated _xs
    (pure values : Eval (List (α × β)))) using
      (fun (row : List value) (pair : α × β) =>
        canons row = canons [toValue pair.1, toValue pair.2])
  trivial

elab "collect_columns" source:term : tactic => withMainContext do
  let source ← Term.elabTerm source none
  Term.synthesizeSyntheticMVarsNoPostponing
  unless ← columnTraversalResult (← instantiateMVars source) do
    throwError "normalized column relation was rejected"

theorem normalizedRows {α β : Type} [ToValue α] [ToValue β]
    (rows : List (List value)) (xs : List (α × β))
    (h : List.Forall₂ (fun row x =>
      canons row = [canon (toValue x.1), canon (toValue x.2)]) rows xs) :
    ∃ left right, collectColumns 2 rows = pure [left, right] ∧
      canons left = canons (xs.map (fun x => toValue x.1)) ∧
      canons right = canons (xs.map (fun x => toValue x.2)) := by
  collect_columns (collectColumns 2 rows)
  exact ⟨_, _, rfl, by assumption, by assumption⟩

/-- info: 'P4SpecTecTest.Tactic.IterationColumns.normalizedRows' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms normalizedRows

elab "projected_inputs" : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← instantiateMVars (← goal.getType)
  let some proof ← columnTraversalInputs
    (evalTactic (← `(tactic| simp_all only [List.map_map, Function.comp_def])))
    (type.getArg! 3) (type.getArg! 4) | throwError "projection inputs rejected"
  goal.assign proof
  replaceMainGoal []

-- A projected column needs only its component encoder, without a product dictionary.
theorem projected {α β : Type} [ToValue α] (raw : List value) (pairs : List (α × β))
    (h : canons raw = canons (pairs.map (fun pair => toValue pair.1))) :
    List.Forall₂ (fun v x => P4SpecTec.Refine.canon v = P4SpecTec.Refine.canon (toValue x))
      raw (pairs.map Prod.fst) := by
  projected_inputs

/-- info: 'P4SpecTecTest.Tactic.IterationColumns.projected' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms projected

end P4SpecTecTest.Tactic.IterationColumns
