import P4SpecTec.Tactic.Refine
import P4SpecTec.Refine.Realize
import P4SpecTec.Tactic.Traversal

/-! Composition of reverse list traversals with explicit intermediate observations. -/

namespace P4SpecTec.Tactic.Realize

open Lean Elab Tactic Meta P4SpecTec.Refine

/-- Pair actual ordered traversals using a checked canonical-input hypothesis.
The supplied output relation retains the actual interpreter intermediates. -/
def traversalGoals (s : SimpSet) (relation : Expr) (source generated : Expr) :
    TacticM Bool := withMainContext do
  let rawHead := chainHead source
  let typedHead := chainHead generated
  unless rawHead.isAppOf ``List.mapM && typedHead.isAppOf ``List.mapM &&
      (chainTail source).isSome && (chainTail generated).isSome do return false
  let some inputs ← columnTraversalInputs (proveValue s)
      rawHead.getAppArgs.back! typedHead.getAppArgs.back!
    | return false
  let q ← Term.exprToSyntax relation
  let h ← Term.exprToSyntax inputs
  if (← columnTraversalRelation source generated).isSome then
    let inputsSyntax ← Term.exprToSyntax typedHead.getAppArgs.back!
    evalTactic (← `(tactic|
      apply Realizes.bind (P := fun outputs results =>
        List.Forall₂ $q outputs results ∧ List.length results = List.length $inputsSyntax)
        (Realizes.mapMWithLength $h ?_)))
  else
    evalTactic (← `(tactic|
      apply Realizes.bind (P := List.Forall₂ $q) (Realizes.mapM $h ?_)))
  return true

end P4SpecTec.Tactic.Realize
