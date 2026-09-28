import P4SpecTec.Tactic.Traversal
import P4SpecTec.Refine.IterationPrem
import P4SpecTec.Refine.IterationLength

/-! Checked positional observations for source list premises with output columns. -/

namespace P4SpecTec.Tactic

open Lean Elab Tactic Meta P4SpecTec.Refine

/-- Retain actual source context constructors around already checked input observations. -/
partial def columnTraversalInputs (prove : TacticM Unit) (raw typed : Expr) :
    TacticM (Option Expr) := withMainContext do
  let raw := raw.consumeMData
  let typed := typed.consumeMData
  if raw.isAppOfArity ``List.zip 4 && typed.isAppOfArity ``List.zip 4 then
    let some left ← columnTraversalInputs prove (raw.getArg! 2) (typed.getArg! 2) | return none
    let some right ← columnTraversalInputs prove (raw.getArg! 3) (typed.getArg! 3) | return none
    return some (← mkAppM ``forall₂Zip #[left, right])
  if let some observed ← traversalInputs prove raw typed then return some observed
  if typed.isAppOfArity ``List.map 4 then
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
      unless (← getGoals).isEmpty do throwError "projected traversal inputs remain unproved"
      setGoals goals
      return some (← mkAppM ``forall₂OfCanons #[encoder, ← instantiateMVars proof])
    catch _ => saved.restore
  if raw.isAppOfArity ``List.map 4 then
    let some observed ← columnTraversalInputs prove (raw.getArg! 3) typed | return none
    return some (← mkAppM ``forall₂MapSource #[raw.getArg! 2, observed])
  return none

/-- The components of a right-nested generated tuple of `count` columns: `x.1, x.2.1, ...`. -/
private partial def columnFields (count : Nat) (type value : Expr) : MetaM (List Expr) := do
  if count == 1 then return [value]
  let type ← whnf type
  unless type.isAppOfArity ``Prod 2 do return []
  let rest ← columnFields (count - 1) (type.getArg! 1) (mkProj ``Prod 1 value)
  return mkProj ``Prod 0 value :: rest

private def columnEncoders (count : Nat) (type : Expr) : MetaM (Option Expr) := do
  if count == 0 then return none
  withLocalDeclD `columnValue type fun value => do
    let fields ← columnFields count type value
    if fields.length != count then return none
    let encoders ← fields.mapM fun field => do
      let encoded ← mkAppM ``P4SpecTec.Prelude.toValue #[field]
      mkLambdaFVars #[value] encoded
    let encoderType ← mkArrow type (mkConst ``P4SpecTec.Lang.Il.value)
    return some (← mkListLit encoderType encoders)

/-- Infer each output encoder from the declared source column count and generated result.
A single column encodes its whole carrier; several columns project the generated tuple. -/
def columnTraversalRelation (source generated : Expr) : TacticM (Option Expr) :=
    withMainContext do
  let sourceHead := chainHead source
  let generatedHead := chainHead generated
  unless sourceHead.isAppOfArity ``List.mapM 6 &&
      generatedHead.isAppOfArity ``List.mapM 6 do return none
  let some continuation := chainTail source | return none
  lambdaTelescope continuation fun arguments body => do
    unless arguments.size == 1 do return none
    let collect := chainHead body
    unless collect.isAppOfArity ``collectColumns 2 do return none
    unless ← isDefEq (collect.getArg! 1) arguments[0]! do return none
    let some count ← getNatValue? (collect.getArg! 0) | return none
    let type := generatedHead.getArg! 3
    let saved ← saveState
    try
      let some encoders ← columnEncoders count type | return none
      let encodersSyntax ← Term.exprToSyntax encoders
      let typeSyntax ← Term.exprToSyntax type
      return some (← Term.elabTerm
        (← `(@P4SpecTec.Refine.ColumnRows $typeSyntax $encodersSyntax)) none)
    catch _ =>
      saved.restore
      return none

private partial def exposeColumnFacts (name : Name) : TacticM Unit := do
  let before ← withMainContext do
    pure ((← getLCtx).foldl (init := #[]) fun ids decl => ids.push decl.fvarId)
  evalTactic (← `(tactic| cases $(mkIdent name):ident))
  let newFacts ← withMainContext do
    let mut facts := []
    for declaration in ← getLCtx do
      if !before.contains declaration.fvarId && !declaration.isImplementationDetail then
        facts := facts ++ [(declaration.userName, declaration.toExpr,
          (← instantiateMVars declaration.type).consumeMData)]
    return facts
  for (_, proof, type) in newFacts do
    if let some (_, left, _) := type.eq? then
      if left.isAppOfArity ``canons 1 then
        withMainContext do
          let proofSyntax ← Term.exprToSyntax proof
          let fact ← freshName "rf_c_column"
          evalTactic (← `(tactic| have $(mkIdent fact):ident := $proofSyntax))
  for (name, _, type) in newFacts do
    if type.isAppOfArity ``List.Forall₂ 5 then
      let encoders := type.getArg! 4
      if encoders.isAppOf ``List.cons || encoders.isAppOf ``List.nil then
        exposeColumnFacts name

/-- Collect a checked batch using the exact per-column encoders in its positional relation. -/
def columnTraversalResult (source : Expr) : TacticM Bool := withMainContext do
  unless source.isAppOfArity ``collectColumns 2 do return false
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let type := (← instantiateMVars declaration.type).consumeMData
    unless type.isAppOfArity ``List.Forall₂ 5 do continue
    unless ← isDefEq (type.getArg! 3) (source.getArg! 1) do continue
    let relation := (type.getArg! 2).consumeMData
    let encoders? ← if relation.isAppOfArity ``ColumnRows 2 then pure (some (relation.getArg! 1))
      else lambdaTelescope relation fun arguments body => do
      unless arguments.size == 2 do return none
      let some (_, left, right) := body.eq? | return none
      unless left.isAppOfArity ``canons 1 do return none
      unless ← isDefEq (left.getArg! 0) arguments[0]! do return none
      if right.isAppOfArity ``canons 1 then
        let values := right.getArg! 0
        if values.isAppOfArity ``List.map 4 then return some (values.getArg! 3)
      let mut values := right
      let mut encoders := []
      while values.isAppOfArity ``List.cons 3 do
        let value := values.getArg! 1
        let value := if value.isAppOfArity ``P4SpecTec.Refine.canon 1 then
            value.getArg! 0 else value
        if value.containsFVar arguments[0]!.fvarId! then return none
        encoders := encoders ++ [← mkLambdaFVars #[arguments[1]!] value]
        values := values.getArg! 2
      unless values.isAppOfArity ``List.nil 1 do return none
      let encoderType ← mkArrow (← inferType arguments[1]!)
        (mkConst ``P4SpecTec.Lang.Il.value)
      return some (← mkListLit encoderType encoders)
    let some encoders := encoders? | continue
    let saved ← saveState
    try
      let proof ← mkAppM ``transposeEncodedRows #[encoders, declaration.toExpr]
      let proofSyntax ← Term.exprToSyntax proof
      let columns ← freshName "rf_columns"
      let equality ← freshName "rf_c_columns"
      let relation ← freshName "rf_g_columns"
      evalTactic (← `(tactic|
        obtain ⟨$(mkIdent columns):ident, $(mkIdent equality):ident,
          $(mkIdent relation):ident⟩ := $proofSyntax))
      withMainContext do
        evalTactic (← `(tactic|
          simp only [List.length_cons, List.length_nil] at $(mkIdent equality):ident))
        evalTactic (← `(tactic| rw [$(mkIdent equality):ident]))
      exposeColumnFacts relation
      return true
    catch _ => saved.restore
  return false

end P4SpecTec.Tactic
