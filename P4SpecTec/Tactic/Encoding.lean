import P4SpecTec.Tactic.Constants
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
  for (name, kind) in ← constantsUnder lib do
    unless !name.isInternal && kind == .defn &&
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

/-- Close one constructor case of a generated subtype-injection bridge
`canon (toValue (up x)) = canon (toValue x)`: unfold the named injection and, repeatedly,
every library encoder occurring in the goal (a resolved instance may belong to an alias),
erase the carrier notes, and, when nested list helpers remain, rewrite them with their
list-map equations proved by induction. The library's encoders are found under `lib`. -/
elab "subtype_canon " lib:ident " [" injections:ident,* "]" : tactic => withoutRecover do
  let lib := lib.getId
  let base := injections.getElems ++ #[mkIdent ``P4SpecTec.Prelude.ToValue.toValue,
    mkIdent ``P4SpecTec.Runtime.Value.Make.case, mkIdent ``P4SpecTec.Runtime.Value.Make.str,
    mkIdent ``P4SpecTec.Refine.canon_make_mk]
  let used (select : Name → Bool) : TacticM (Array Name) := withMainContext do
    let goal ← instantiateMVars (← getMainTarget)
    pure (goal.getUsedConstants.filter fun name => lib.isPrefixOf name && select name)
  let mut extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  let mut proved : Array Name := #[]
  for _ in [0:8] do
    if (← getGoals).isEmpty then return
    let encoders ← used (·.getString! == "toValue")
    let names := base ++ encoders.map mkIdent
    let lemmas ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $n:ident)
    let rules : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems (lemmas ++ extra)
    unless ← tryTac (evalTactic (← `(tactic| simp only [$rules,*]))) do
      -- nothing left to unfold: prove the nested list helpers' list-map equations
      let helpers := (← used (·.getString!.startsWith "toValue_")).filter (!proved.contains ·)
      if helpers.isEmpty then break
      for helper in helpers do
        proved := proved.push helper
        let some encoder ← listEncoder? helper | continue
        let fact ← freshName "rf_c_encoding"
        let enc ← withMainContext do Term.exprToSyntax encoder
        evalTactic (← `(tactic|
          have $(mkIdent fact):ident : ∀ xs, $(mkIdent helper):ident xs = List.map $enc xs := by
            intro xs
            induction xs <;> simp_all [$(mkIdent helper):ident]))
        extra := extra.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent fact):ident))
  unless (← getGoals).isEmpty do throwError "subtype_canon: canonical encodings differ"

/-- Two library encoders of the same generated value agree canonically (`canon (A x) =
canon (B x)`), as a recursive group's nested helper encoders and the generic instance
encoders do: split the value at its constructor, unfold both encoders, rewrite nested list
helpers by their list-map equations (proved by induction) and compare list elements
pointwise, to a bounded nesting depth. Every step is a checked rewrite of the actual goal. -/
partial def encodingCoherence (depth : Nat := 4) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  if depth == 0 then throwError "encoding coherence: nesting depth exhausted"
  let lib ← libOf
  let used (select : Name → Bool) : TacticM (Array Name) := withMainContext do
    let goal ← instantiateMVars (← getMainTarget)
    pure (goal.getUsedConstants.filter fun name =>
      lib.isPrefixOf name && !name.isInternal && select name)
  let unfold : TacticM Unit := do
    for _ in [0:6] do
      if (← getGoals).isEmpty then return
      let encoders ← used fun n => (n.toString.splitOn ".toValue").length > 1 ||
        (n.toString.splitOn "instToValue").length > 1
      let names := encoders ++ #[``P4SpecTec.Prelude.ToValue.toValue,
        ``P4SpecTec.Prelude.instToValueList, ``P4SpecTec.Runtime.Value.Make.case,
        ``P4SpecTec.Runtime.Value.Make.list, ``P4SpecTec.Runtime.Value.Make.text,
        ``P4SpecTec.Refine.canon_make_mk, ``P4SpecTec.Refine.canon_mk, ``P4SpecTec.Refine.canon',
        ``P4SpecTec.Refine.canonMixfix, ``P4SpecTec.Refine.canonMixfixes]
      let lemmas ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
      let rules : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems lemmas
      unless ← tryTac (evalTactic (← `(tactic| simp only [$rules,*]))) do return
  let helperFacts : TacticM Unit := do
    for helper in ← used (·.getString!.startsWith "toValue_") do
      let some encoder ← listEncoder? helper | continue
      let fact ← freshName "rz_encoding"
      let enc ← withMainContext do Term.exprToSyntax encoder
      evalTactic (← `(tactic|
        have $(mkIdent fact):ident : ∀ xs, $(mkIdent helper):ident xs = List.map $enc xs := by
          intro xs
          induction xs <;> simp_all [$(mkIdent helper):ident]))
      let _ ← tryTac (evalTactic (← `(tactic| simp only [$(mkIdent fact):ident])))
  unfold
  if (← getGoals).isEmpty then return
  if ← tryTac (evalTactic (← `(tactic| rfl))) then return
  helperFacts
  if (← getGoals).isEmpty then return
  -- canonical constructor payloads: compare nested lists of the same elements pointwise
  let _ ← tryTac (evalTactic (← `(tactic|
    simp only [P4SpecTec.Lang.Il.value'.CaseV.injEq, P4SpecTec.Lang.Il.value'.ListV.injEq,
      P4SpecTec.Util.Source.info.mk.injEq, P4SpecTec.Domain.Mixfix.t.Brack.injEq,
      P4SpecTec.Domain.Mixfix.t.Arg.injEq, P4SpecTec.Domain.Mixfix.t.Seq.injEq,
      and_true, true_and, List.cons.injEq])))
  if (← getGoals).isEmpty then return
  if ← tryTac (evalTactic (← `(tactic| apply P4SpecTec.Refine.canons_map_congr))) then
    let x ← freshName "rz_element"
    let hx ← freshName "rz_member"
    evalTactic (← `(tactic| intro $(mkIdent x):ident $(mkIdent hx):ident))
    return ← encodingCoherence (depth - 1)
  -- otherwise split the encoded generated value at its constructor and unfold again
  let value? ← withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some (_, lhs, _) := target.eq? | return none
    let lhs := lhs.consumeMData
    unless lhs.isAppOfArity ``P4SpecTec.Refine.canon 1 do return none
    match (lhs.getArg! 0).consumeMData.getAppArgs.back? with
    | some argument => match argument.consumeMData with
      | .fvar f => return some f
      | _ => return none
    | none => return none
  let some value := value? |
    throwError
      "encoding coherence: no encoded variable to split{Lean.MessageData.ofGoal (← getMainGoal)}"
  -- by its id: a variable left by an earlier split has an inaccessible name
  let subgoals ← (← getMainGoal).cases value
  for g in subgoals.map (·.mvarId) do
    setGoals [g]
    encodingCoherence (depth - 1)

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
