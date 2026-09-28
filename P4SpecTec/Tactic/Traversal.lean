import P4SpecTec.Tactic.Refine.Context
import P4SpecTec.Refine.Iteration
import P4SpecTec.Refine.IterationColumns
import P4SpecTec.Refine.RealizeIteration

/-! Direction-independent positional observations for actual interpreter traversals. -/

namespace P4SpecTec.Tactic

open Lean Elab Tactic Meta P4SpecTec.Refine

/-- Construct positional input relations from actual canonical observations and zips. -/
partial def traversalInputs (prove : TacticM Unit) (raw typed : Expr) :
    TacticM (Option Expr) := withMainContext do
  let raw := raw.consumeMData
  let typed := typed.consumeMData
  if raw.isAppOfArity ``List.zip 4 && typed.isAppOfArity ``List.zip 4 then
    let some left ← traversalInputs prove (raw.getArg! 2) (typed.getArg! 2) | return none
    let some right ← traversalInputs prove (raw.getArg! 3) (typed.getArg! 3) | return none
    return some (← mkAppM ``forall₂Zip #[left, right])
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty := (← instantiateMVars decl.type).consumeMData
    if let some (_, lhs, rhs) := ty.eq? then
      let lhs := lhs.consumeMData
      let rhs := rhs.consumeMData
      if lhs.isAppOfArity ``canons 1 && rhs.isAppOfArity ``canons 1 then
        let mapped := rhs.getArg! 0
        if mapped.isAppOfArity ``List.map 4 then
          if (← isDefEq (lhs.getArg! 0) raw) && (← isDefEq (mapped.getArg! 3) typed) then
            return some (← mkAppM ``forall₂OfCanons #[mapped.getArg! 2, decl.toExpr])
  if (raw.isAppOf ``List.cons && typed.isAppOf ``List.cons) ||
      (raw.isAppOf ``List.nil && typed.isAppOf ``List.nil) then
    let saved ← saveState
    try
      let rawSyntax ← Term.exprToSyntax raw
      let typedSyntax ← Term.exprToSyntax typed
      let type ← whnf (← inferType typed)
      let elementSyntax ← Term.exprToSyntax (type.getArg! 0)
      let encoder ← Term.elabTerm
        (← `(fun x : $elementSyntax => P4SpecTec.Prelude.toValue x)) none
      let proposition ← Term.elabTerm (← `(canons $rawSyntax =
        canons (List.map P4SpecTec.Prelude.toValue $typedSyntax))) (some (mkSort .zero))
      let proof ← mkFreshExprMVar proposition
      let goals ← getGoals
      setGoals [proof.mvarId!]
      prove
      unless (← getGoals).isEmpty do throwError "literal traversal inputs remain unproved"
      setGoals goals
      return some (← mkAppM ``forall₂OfCanons #[encoder, ← instantiateMVars proof])
    catch _ => saved.restore
  return none

/-- Rewrite completed batches whose actual output relation proves every row is empty. -/
def emptyTraversalResult (source : Expr) : TacticM Bool := withMainContext do
  -- a batch without outputs: every row is empty
  if source.isAppOfArity ``collectColumns 2 then
    let some 0 ← getNatValue? (source.getArg! 0) | return false
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      unless ty.isAppOfArity ``List.Forall₂ 5 do continue
      unless ← isDefEq (ty.getArg! 3) (source.getArg! 1) do continue
      if ← tryTac (evalTactic (← `(tactic|
          rw [collectColumnsNoOutputs $(mkIdent decl.userName):ident]))) then return true
    return false
  unless source.isAppOfArity ``P4SpecTec.Interp_al.Ctx.transpose 1 do return false
  let mut rows := source.getArg! 0
  let mut count := 0
  while rows.isAppOfArity ``List.cons 3 && (rows.getArg! 1).isAppOf ``List.nil do
    count := count + 1
    rows := rows.getArg! 2
  let mut names := []
  for decl in ← getLCtx do
    let ty := (← instantiateMVars decl.type).consumeMData
    if ty.isAppOfArity ``List.Forall₂ 5 then
      if ← isDefEq (ty.getArg! 3) rows then names := decl.userName :: names
  let countSyntax := Syntax.mkNumLit (toString count)
  for name in names do
    let fact ← freshName "rf_c_empty"
    if ← tryTac do
        evalTactic (← `(tactic|
          have $(mkIdent fact):ident :=
            transposeRelatedEmptyPrefix $countSyntax $(mkIdent name):ident))
        withMainContext do
          evalTactic (← `(tactic|
            simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
              at $(mkIdent fact):ident))
          evalTactic (← `(tactic| rw [$(mkIdent fact):ident]))
      then return true
  return false


end P4SpecTec.Tactic
