import P4SpecTec.Tactic.Refine.Normalize
import P4SpecTec.Tactic.RunSound

/-! Proved list-map equations for generated recursive value encoders. -/

namespace P4SpecTec.Tactic

open Lean Elab Tactic Meta

/-- Read a unary list encoder's element function from an actual constructor equation. -/
def listEncoder? (name : Name) : MetaM (Option Expr) := do
  let info ← getConstInfo name
  let unary ← forallTelescopeReducing info.type fun xs result => do
    if xs.size != 1 then return false
    let input ← inferType xs[0]!
    return input.isAppOfArity ``List 1 && result.isAppOfArity ``List 1 &&
      (result.getArg! 0).isConstOf ``P4SpecTec.Lang.Il.value
  unless unary do return none
  let some equations ← getEqnsFor? name | return none
  for equation in equations do
    let found ← forallTelescopeReducing (← getConstInfo equation).type fun _ conclusion => do
      let some (_, lhs, rhs) := conclusion.eq? | return none
      unless lhs.isAppOfArity name 1 && rhs.isAppOfArity ``List.cons 3 do return none
      let input := lhs.getArg! 0
      unless input.isAppOfArity ``List.cons 3 do return none
      let head := input.getArg! 1
      unless head.isFVar do return none
      let encoder ← mkLambdaFVars #[head] (rhs.getArg! 1)
      if encoder.hasFVar then return none
      return some encoder
    if found.isSome then return found
  return none

/-- Establish list-map equations by induction; every proposed encoder equation is checked. -/
def encodingFacts (lib : Name) : TacticM Unit := withMainContext do
  let candidates := (← getEnv).constants.map₂.toList ++ (← getEnv).constants.map₁.toList
  for (name, info) in candidates do
    unless lib.isPrefixOf name && !name.isInternal && info.isDefinition &&
        name.getString!.startsWith "toValue_" do continue
    let some encoder ← listEncoder? name | continue
    let fact ← freshName "rf_c_encoding"
    let enc ← Term.exprToSyntax encoder
    let eqns ← eqnsOf name
    let args ← eqns.toArray.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    let rules : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems args
    withMainContext do
      evalTactic (← `(tactic|
        have $(mkIdent fact):ident : ∀ xs, $(mkIdent name):ident xs = List.map $enc xs := by
          intro xs
          induction xs with
          | nil => simp only [$rules,*, List.map_nil]
          | cons x xs ih =>
            simpa only [$rules,*, List.map_cons] using congrArg (List.cons ($enc x)) ih))

/-- Related raw lists have the lengths of their explicitly encoded typed lists. -/
def encodingLengths : TacticM Unit := do
  let facts ← withMainContext do
    let mut facts := []
    for d in ← getLCtx do
      let ty := (← instantiateMVars d.type).consumeMData
      if let some (_, lhs, rhs) := ty.eq? then
        if lhs.isAppOfArity ``P4SpecTec.Refine.canons 1 &&
            rhs.isAppOfArity ``P4SpecTec.Refine.canons 1 then
          let name := Name.mkSimple s!"rf_c_length{d.index}"
          unless ((← getLCtx).findFromUserName? name).isSome do
            facts := (d.userName, name) :: facts
    pure facts
  for (source, name) in facts do
    traceStep m!"related list length from {source}"
    withMainContext do
      evalTactic (← `(tactic|
        have $(mkIdent name):ident := congrArg List.length $(mkIdent source):ident))
    withMainContext do
      evalTactic (← `(tactic|
        try simp only [P4SpecTec.Refine.canons_length, List.length_map]
          at $(mkIdent name):ident))

/-- Recover whole-value canonical facts from exposed compound-encoder payload equations.
This keeps `canon` abstract in the global rules while transporting the checked payload
shape, including arbitrary source metadata, back to its canonical value. -/
def encodingShapes : TacticM Unit := do
  let facts ← withMainContext do
    let mut facts := []
    for d in ← getLCtx do
      unless d.userName.toString.startsWith "rf_h" do continue
      let ty := (← instantiateMVars d.type).consumeMData
      let some (_, lhs, rhs) := ty.eq? | continue
      let lhs := lhs.consumeMData
      let payload := if lhs.isAppOfArity ``P4SpecTec.Util.Source.info.it 4 then
          some (lhs.getArg! 3)
        else match lhs with
          | .proj ``P4SpecTec.Util.Source.info 0 value => some value
          | _ => none
      let some payload := payload | continue
      if payload.consumeMData.isFVar then continue
      let name := Name.mkSimple s!"rf_c_shape{d.index}"
      facts := (name, payload, rhs, d.toExpr) :: facts
    pure facts
  for (name, value, shape, proof) in facts do
    withMainContext do
      let v ← Term.exprToSyntax value
      let p ← Term.exprToSyntax shape
      let h ← Term.exprToSyntax proof
      unless ((← getLCtx).findFromUserName? name).isSome do
        evalTactic (← `(tactic| have $(mkIdent name):ident := $h))
      let canonical ← freshName "rz_shape"
      evalTactic (← `(tactic|
        have $(mkIdent canonical):ident : P4SpecTec.Refine.canon $v =
            P4SpecTec.Refine.canon
              ⟨$p, P4SpecTec.Refine.dummy, P4SpecTec.Util.Source.no_region⟩ := by
          simpa only [P4SpecTec.Refine.canon] using
            congrArg (fun payload => (⟨P4SpecTec.Refine.canon' payload,
              P4SpecTec.Refine.dummy, P4SpecTec.Util.Source.no_region⟩ : P4SpecTec.Lang.Il.value))
              $h))
      withMainContext do
        evalTactic (← `(tactic| simp only [$(mkIdent canonical):ident] at *))
      if (← getGoals).isEmpty then return
      let _ ← tryTac (evalTactic (← `(tactic| clear $(mkIdent canonical):ident)))

end P4SpecTec.Tactic
