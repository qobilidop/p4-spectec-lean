import P4SpecTec.Tactic.Refine
import P4SpecTec.Refine.Realize
import P4SpecTec.Tactic.Traversal
import P4SpecTec.Refine.RealizeIteration

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
      (chainTail source).isSome do return false
  let some inputs ← columnTraversalInputs (proveValue s)
      rawHead.getAppArgs.back! typedHead.getAppArgs.back!
    | return false
  -- a generated traversal that ends the computation continues with `pure`
  if (chainTail generated).isNone then evalTactic (← `(tactic| apply Realizes.ofBindPure))
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

/-- Pair a reference traversal producing values (an iterated expression) with a pure
generated `List.map` inside the generated head, when their input lists are positionally
related. The generated side takes no step; the continuation receives the related results. -/
def pureMapTraversal (s : SimpSet) (source generated : Expr) : TacticM Bool :=
    withMainContext do
  let rawHead := chainHead source
  unless rawHead.isAppOfArity ``List.mapM 6 && (chainTail source).isSome do return false
  unless ← isDefEq (rawHead.getArg! 3) (mkConst ``P4SpecTec.Lang.Il.value) do return false
  let typedHead := chainHead generated
  if typedHead.isAppOf ``List.mapM then return false
  -- the map may already be bound by a generated `have` whose defining fact is in context
  let bound ← (← getLCtx).foldlM (init := #[]) fun found decl => do
    if decl.isImplementationDetail then return found
    return found ++ (closedMaps (← instantiateMVars decl.type)).toArray
  for candidate in closedMaps typedHead ++ closedMaps generated ++ bound.toList do
    let saved ← saveState
    try
      let some inputs ← columnTraversalInputs (proveValue s) rawHead.getAppArgs.back!
          (candidate.getArg! 3) | throwError "unrelated inputs"
      let h ← Term.exprToSyntax inputs
      let c ← Term.exprToSyntax candidate
      let element ← Term.exprToSyntax (candidate.getArg! 1)
      traceStep m!"reverse pure generated map {candidate}"
      evalTactic (← `(tactic|
        apply Realizes.bindPure (c := $c)
          (P := List.Forall₂ (@P4SpecTec.Refine.Rel $element _)) (Realizes.mapMPureMap $h ?_)))
      return true
    catch _ => saved.restore
  return false

end P4SpecTec.Tactic.Realize
