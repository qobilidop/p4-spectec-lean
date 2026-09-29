import P4SpecTec.Tactic.Refine
import P4SpecTec.Tactic.Encoding
import P4SpecTec.Tactic.RealizeTraversal
import P4SpecTec.Refine.RealizeChoice
import P4SpecTec.Refine.RealizeFuel
import P4SpecTec.Refine.RealizeInterp
import P4SpecTec.Refine.Subtype

/-!
Reverse symbolic execution over fuel families. The driver combines independently
constructed eventual witnesses; it does not use forward refinement theorems.
Recursive calls consume the generated fixed point's outcome induction hypothesis.
-/

namespace P4SpecTec.Tactic.Realize

open Lean Elab Tactic Meta
open P4SpecTec.Refine P4SpecTec.Prelude P4SpecTec.Interp_al

/-- The relation, reference fuel family and generated computation of the goal. -/
def goalParts : TacticM (Expr × Expr × Expr) := withMainContext do
  let ty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless ty.isAppOfArity ``Realizes 5 do
    throwError "realize_al: expected Realizes, got {ty}"
  return (ty.getArg! 2, ty.getArg! 3, ty.getArg! 4)

/-- Discharge the explicit environment and representation premises of a callee. -/
def premises (s : SimpSet) : TacticM Unit := do
  let goals ← getGoals
  for g in goals do
    setGoals [g]
    if ← tryTac (evalTactic (← `(tactic| assumption))) then continue
    let _ ← normalize s
    if (← getGoals).isEmpty then continue
    if ← tryTac (evalTactic (← `(tactic| assumption))) then continue
    if ← declarationFromSpec then continue
    proveValue s
  setGoals []

/-- Remove a known fixed fuel offset at an abstract invocation using eventuality. -/
def calleeFuel : TacticM Unit := withMainContext do
  let (relation, reference, generated) ← goalParts
  withLocalDeclD `rz_fuel (mkConst ``Nat) fun fuel => do
    let source := (mkApp reference fuel).headBeta.consumeMData
    let some amount ← fuelArgument? source
      | throwError "realize_al: callee has no fuel argument"
    if amount == fuel then return
    let offset ← whnf (amount.replace fun e => if e == fuel then some (mkNatLit 0) else none)
    if offset.hasFVar then throwError "realize_al: callee fuel is not a fixed offset"
    let args := source.getAppArgs.map fun a => if a == amount then fuel else a
    let base ← mkLambdaFVars #[fuel] (mkAppN source.getAppFn args)
    let wanted ← mkAppM ``Realizes #[relation, base, generated]
    let h ← mkFreshExprMVar wanted
    let proof ← mkAppM ``Realizes.add #[h, offset]
    let goal ← getMainGoal
    unless ← isDefEq (← inferType proof) (← goal.getType) do
      throwError "realize_al: fuel offset transport failed"
    goal.assign proof
    replaceMainGoal [h.mvarId!]

/-- Apply the recursive outcome induction hypothesis or a checked callee certificate. -/
def callee (s : SimpSet) (generated : Expr) : TacticM Unit := withMainContext do
  -- a callee invoked at the unshifted fuel has no offset to reassociate
  let _ ← tryTac (evalTactic (← `(tactic| simp only [Nat.add_assoc])))
  calleeFuel
  unless generated.isAppOfArity ``ExceptT.mk 4 do
    throwError "realize_al: expected generated callee, got {generated}"
  let call := (generated.getArg! 3).consumeMData
  match call.getAppFn.consumeMData with
  | .fvar f =>
    let some (ih, _) ← ihFor f
      | throwError "realize_al: no outcome induction hypothesis for {call.getAppFn}"
    let args ← call.getAppArgs.mapM fun a => Term.exprToSyntax a
    let q ← freshName "rz_q"
    let hq ← freshName "rz_hq"
    evalTactic (← `(tactic| intro $(mkIdent q):ident $(mkIdent hq):ident))
    evalTactic (← `(tactic| apply $(mkIdent ih):ident $args*
      $(mkIdent q):ident $(mkIdent hq):ident))
  | .const name _ =>
    let owner := if name.getString! == "run" then name.getPrefix else name
    evalTactic (← `(tactic| apply $(mkIdent (owner ++ `realizes)):ident))
  | _ => throwError "realize_al: unsupported callee {call}"
  premises s

/-- Select a generated discriminant without inspecting a reference fuel binder. -/
def splitData (e : Expr) : TacticM Bool := do
  if let some v ← stuckOn e then
    let name ← withMainContext do pure (← v.getDecl).userName
    traceStep m!"reverse cases {name}: {← withMainContext do v.getType}"
    -- by `FVarId`: a hygienic user name can resolve to another variable of that name
    return ← tryTac do
      let goals ← (← getMainGoal).cases v
      replaceMainGoal (goals.map (·.mvarId)).toList
  return false

/-- Prove an equality fact separately, retaining the exact reverse goal and its context. -/
def equalityFact (s : SimpSet) (name : Name) (lhs rhs : Expr)
    (rule : Name) (negative : Bool := false) : TacticM Unit := withMainContext do
  let main ← getMainGoal
  let proposition ← mkEq lhs rhs
  let proof ← mkFreshExprMVar proposition
  setGoals [proof.mvarId!]
  evalTactic (← `(tactic| apply $(mkIdent rule):ident))
  if negative then
    let hn ← freshName "rz_ne"
    evalTactic (← `(tactic| intro $(mkIdent hn):ident))
    let _ ← normalizeAt s hn
    if !(← getGoals).isEmpty then
      evalTactic (← `(tactic| cases $(mkIdent hn):ident))
  else
    for g in ← getGoals do
      setGoals [g]
      proveValue s
  pruneSolvedGoals
  unless (← getGoals).isEmpty do throwError "realize_al: canonical fact remains unproved"
  let next ← main.assert name proposition (← instantiateMVars proof)
  let (_, next) ← next.intro1P
  setGoals [next]

/-- Align source equality tests with generated tests using checked canonical relations. -/
def alignTests (s : SimpSet) (source generated : Expr)
    (useFacts : Bool := false) : TacticM Bool := do
  let tests := (valueEqs source).eraseDups
  let counterparts := (valueEqs generated).eraseDups
  let facts ← withMainContext do
    let mut tests := []
    for d in ← getLCtx do
      if d.userName.toString.startsWith "rf_c" then
        tests := tests ++ valueEqs (← instantiateMVars d.type)
    pure tests.eraseDups
  for (a, i) in tests.zipIdx do
    let h ← freshName "rz_eq"
    let finish : TacticM Unit := withMainContext do
      evalTactic (← `(tactic| simp only [$(mkIdent h):ident]))
    if ← tryTac do
        equalityFact s h a (mkConst ``Bool.true) ``eq_true_of_canon
        finish then return true
    if ← tryTac do
        equalityFact s h a (mkConst ``Bool.false) ``eq_false_of_canon true
        finish then return true
    if tests.length == counterparts.length then
      if ← tryTac do
          equalityFact s h a counterparts[i]! ``eq_of_canon
          finish then return true
    for b in (if useFacts then facts else []) do
      if ← tryTac do
          equalityFact s h a b ``eq_of_canon
          finish then return true
  return false

/-- Discharge equality guards whose encoded constructor shapes are now exposed. -/
def canonicalConditions (s : SimpSet) : TacticM Unit := do
  let facts ← withMainContext do
    let mut facts := []
    for d in ← getLCtx do
      if d.userName.toString.startsWith "rf_c" then
        for test in (valueEqs (← instantiateMVars d.type)).eraseDups do
          facts := (d.userName, test) :: facts
    pure facts
  for (guard, test) in facts do
    if (← getGoals).isEmpty then return
    let _ := test
    -- a guard in another form (a negation, or `= false`) is left to normalization
    let _ ← tryTac (withMainContext do
      evalTactic (← `(tactic| simp only [eq_iff_canon] at $(mkIdent guard):ident)))
    let _ ← normalizeAt s guard

/-- Introduce one accessible binder, preserving representation equalities as facts. -/
def introOne (s : SimpSet) (conjunctions : Bool := false) : TacticM Unit := do
  let g ← getMainGoal
  let ty ← g.withContext do whnfR (← g.getType)
  let .forallE name _ _ _ := ty | throwError "realize_al: expected binder"
  let name ← freshName (if name.isAnonymous then "rz_x" else name.toString)
  evalTactic (← `(tactic| intro $(mkIdent name):ident))
  if conjunctions then elementResults name
  -- a batch's column relation keeps its encoders for column collection
  if conjunctions && (← columnRelationHyp name) then
    let _ ← tryTac (evalTactic (← `(tactic| dsimp only at $(mkIdent name):ident)))
  else
    let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel, Outs] at $(mkIdent name):ident)))
    let _ ← normalizeAt s name
  if conjunctions && !(← getGoals).isEmpty then
    let conjunction ← withMainContext do
      let some decl := (← getLCtx).findFromUserName? name | return false
      return (← whnf (← instantiateMVars decl.type)).isAppOfArity ``And 2
    if conjunction then
      let left ← freshName "rf_g_left"
      let isLength ← withMainContext do
        let some declaration := (← getLCtx).findFromUserName? name | return false
        let type ← whnf (← instantiateMVars declaration.type)
        let some (_, lhs, _) := (type.getArg! 1).eq? | return false
        return lhs.isAppOfArity ``List.length 2
      let right ← freshName (if isLength then "rf_c_traversalLength" else "rf_g_right")
      evalTactic (← `(tactic|
        obtain ⟨$(mkIdent left):ident, $(mkIdent right):ident⟩ := $(mkIdent name):ident))
  pure ()

/-- A generated emptiness test after the reference side already reached its outcome:
split the generated list, so each branch's related reference value is exposed. -/
def splitGeneratedList (genHead : Expr) : TacticM Bool := do
  let goal ← getMainGoal
  let some f ← goal.withContext (generatedListTest? genHead) | return false
  traceStep m!"cases {← goal.withContext do pure (← f.getDecl).userName} (generated list test)"
  replaceMainGoal ((← goal.cases f).map (·.mvarId)).toList
  return true

/-- Compose one reverse step, retaining the local fuel offset in the reference family. -/
partial def step (s : SimpSet) (remaining : Nat := 300)
    (relations : Bool := false) (iterRel : Option Expr := none) : TacticM Unit := do
  pruneSolvedGoals
  if (← getGoals).isEmpty then return
  withMainContext do
    if remaining == 0 then throwError "realize_al: symbolic step limit reached"
    let _ ← normalize s
    if (← getGoals).isEmpty then return
    normalizeFacts s
    if (← getGoals).isEmpty then return
    if relations then
      canonicalConditions s
      if !(← getGoals).isEmpty then encodingShapes
      normalizeFacts s
      if !(← getGoals).isEmpty then encodingLengths
      if !(← getGoals).isEmpty then
        if let some f ← relatedOption then
          let name ← withMainContext do pure (← f.getDecl).userName
          evalTactic (← `(tactic| cases $(mkIdent name):ident))
          let goals ← getGoals
          for g in goals do
            setGoals [g]
            step s (remaining - 1) relations iterRel
          setGoals []
          return
    if (← getGoals).isEmpty then return
    let beforeExpose ← getGoals
    expose
    if (← getGoals).isEmpty then return
    -- Newly exposed constructors must reduce before selecting another discriminant.
    if (← getGoals) != beforeExpose then return ← step s (remaining - 1) relations iterRel
    if ← tryTac (evalTactic (← `(tactic| contradiction))) then return
    if ← closeArithmetic then return
    let ty ← withMainContext do whnfR (← instantiateMVars (← (← getMainGoal).getType))
    if ty.isForall then
      introOne s relations
      return ← step s (remaining - 1) relations iterRel
    if ← tableFacts (← libOf) then return ← step s (remaining - 1) relations iterRel
    let (_, reference, generated) ← goalParts
    withMainContext <| withLocalDeclD `rz_fuel (mkConst ``Nat) fun fuel => do
      let source := (mkApp reference fuel).headBeta.consumeMData
      let head := chainHead source
      let genHead := chainHead generated
      if relations then
        if ← emptyTraversalResult head then
          return ← step s (remaining - 1) relations iterRel
        if ← columnTraversalResult head then
          return ← step s (remaining - 1) relations iterRel
        if head.isAppOfArity ``Ctx.transpose 1 then
          if ← normalize s then return ← step s (remaining - 1) relations iterRel
      traceStep m!"reverse {remaining}: {head.getAppFn} / {genHead.getAppFn}"
      -- checked local lookups over pattern-assigned contexts, whatever the pairing relation
      if ← lookupTraversalAt s source then
        return ← step s (remaining - 1) relations iterRel
      let traversalRelation ← match iterRel with
        -- with relation presets, the source-derived relation observes pattern traversals
        -- (contexts); other traversals keep their own element relations below
        | some relation =>
          if !relations then pure (some relation)
          else if head.isAppOfArity ``List.mapM 6 &&
              (← isDefEq (head.getArg! 3) (mkConst ``P4SpecTec.Interp_al.Ctx.t)) then
            pure (some relation)
          else
            let columnRelation ← columnTraversalRelation source generated
            if let some relation := columnRelation then pure (some relation)
            else if head.isAppOfArity ``List.mapM 6 && genHead.isAppOfArity ``List.mapM 6 &&
                (← isDefEq (head.getArg! 3) (mkConst ``P4SpecTec.Lang.Il.value)) then
              let element ← Term.exprToSyntax (genHead.getArg! 3)
              pure (some (← Term.elabTerm (← `(@P4SpecTec.Refine.Rel $element _)) none))
            else pure none
        | none =>
          let columnRelation ←
            if relations then columnTraversalRelation source generated else pure none
          if let some relation := columnRelation then pure (some relation)
          else if relations && head.isAppOfArity ``List.mapM 6 &&
              genHead.isAppOfArity ``List.mapM 6 then
            if (← isDefEq (head.getArg! 3) (mkApp (mkConst ``List [Level.zero])
                (mkConst ``P4SpecTec.Lang.Il.value))) &&
                (← isDefEq (genHead.getArg! 3) (mkConst ``Unit)) then
              pure (some (← Term.elabTerm
                (← `(fun (row : List P4SpecTec.Lang.Il.value) (_ : Unit) => row = [])) none))
            -- an iterated expression: each reference element value represents its generated one
            else if ← isDefEq (head.getArg! 3) (mkConst ``P4SpecTec.Lang.Il.value) then
              let element ← Term.exprToSyntax (genHead.getArg! 3)
              pure (some (← Term.elabTerm (← `(@P4SpecTec.Refine.Rel $element _)) none))
            else pure none
          else pure none
      if let some relation := traversalRelation then
        if ← lookupTraversalAt s source then
          return ← step s (remaining - 1) relations iterRel
        if ← traversalGoals s relation source generated then
          let goals ← getGoals
          for g in goals do
            setGoals [g]
            step s (remaining - 1) relations iterRel
          setGoals []
          return
      if relations then
        if ← pureMapTraversal s source generated then
          let goals ← getGoals
          for g in goals do
            setGoals [g]
            step s (remaining - 1) relations iterRel
          setGoals []
          return
      -- Differing terminal outcomes can only occur in a branch whose decided tests conflict.
      let terminal (e : Expr) := e.isAppOfArity ``Pure.pure 4 || e.isAppOfArity ``throw 5
      if terminal head && terminal genHead &&
          head.getAppFn.constName? != genHead.getAppFn.constName? then
        if ← closeBoolConflict then return
        if ← closeConstructorClash then return
        if ← closeValueEqConflict s then return
        if ← splitFactList s (step s (remaining - 1) relations iterRel) then return
      if generated.isAppOfArity ``letFun 4 then
        evalTactic (← `(tactic| apply Realizes.have))
      else if source.isAppOfArity ``Eval.orElse 3 then
        unless generated.isAppOfArity ``Eval.orElse 3 do
          throwError "realize_al: ordered-choice shapes differ"
        evalTactic (← `(tactic| apply Realizes.orElse))
      else if head.isAppOfArity ``Pure.pure 4 && (chainTail source).isNone &&
          (!relations ||
            (genHead.isAppOfArity ``Pure.pure 4 && (chainTail generated).isNone)) then
        evalTactic (← `(tactic| apply Realizes.pure))
        if !(← getGoals).isEmpty then proveValue s
      else if head.isAppOfArity ``throw 5 && (chainTail source).isNone &&
          (!relations ||
            (genHead.isAppOfArity ``throw 5 && (chainTail generated).isNone)) then
        evalTactic (← `(tactic| exact Realizes.error _ _))
      else if invocations.any (head.isAppOf ·) && genHead.isAppOfArity ``ExceptT.mk 4 then
        let saved ← getGoals
        if (chainTail source).isSome then
          if (chainTail generated).isNone then
            evalTactic (← `(tactic| apply Realizes.ofBindPure))
          evalTactic (← `(tactic| apply Realizes.bind))
          let gs ← getGoals
          let first := gs.head!
          let rest := gs.tail!
          setGoals [first]
          callee s genHead
          setGoals rest
        else
          callee s genHead
        if (← getGoals).isEmpty then return
        if (← getGoals) == saved then throwError "realize_al: callee made no progress"
      else if (← stuckFuel head).isSome then
        evalTactic (← `(tactic| apply Realizes.ofAdd 1))
      else if relations &&
          ((head.isAppOfArity ``ite 5 && !(valueEqs (head.getArg! 1)).isEmpty) ||
           (genHead.isAppOfArity ``ite 5 && !(valueEqs (genHead.getArg! 1)).isEmpty)) then
        if ← alignTests s head genHead relations then
          return ← step s (remaining - 1) relations iterRel
        if ← alignTests s genHead genHead relations then
          return ← step s (remaining - 1) relations iterRel
        let c := if head.isAppOfArity ``ite 5 then head.getArg! 1 else genHead.getArg! 1
        let stx ← Term.exprToSyntax c
        let h ← freshName "rf_c"
        evalTactic (← `(tactic| by_cases $(mkIdent h):ident : $stx:term))
      -- a generated test and the reference test of the same step, decided together
      else if ← (if (chainHead source).containsFVar fuel.fvarId! then pure false
          else alignTest s source generated) then pure ()
      else if ← splitData genHead then pure ()
      else if ← splitData head then pure ()
      -- `(← ·)` would be lifted out of `&&`; the split must run only after the outcome, or
      -- once the reference side has decided its own test and moved on to an invocation
      else if ← (if terminal head || invocations.any (head.isAppOf ·) then
          splitGeneratedList genHead else pure false) then pure ()
      else
        let cond? := if head.isAppOfArity ``ite 5 then some (head.getArg! 1)
          else if genHead.isAppOfArity ``ite 5 then some (genHead.getArg! 1) else none
        if let some c := cond? then
          if ← alignTests s head genHead relations then
            return ← step s (remaining - 1) relations iterRel
          if ← alignTests s genHead genHead relations then
            return ← step s (remaining - 1) relations iterRel
          let stx ← Term.exprToSyntax c
          let h ← freshName "rf_c"
          evalTactic (← `(tactic| by_cases $(mkIdent h):ident : $stx:term))
        else if ← tryTac (evalTactic (← `(tactic| split))) then pure ()
        -- a branch whose decided facts conflict (a constructor clash such as
        -- `ListV [] = ListV (_ :: _)`) is impossible
        else if ← closeBoolConflict then return
        else if ← closeConstructorClash then return
        else if ← closeValueEqConflict s then return
        else if ← splitFactList s (step s (remaining - 1) relations iterRel) then return
        else
          throwError "realize_al: stuck at {head} against {genHead}\
            {Lean.MessageData.ofGoal (← getMainGoal)}"
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        step s (remaining - 1) relations iterRel
      setGoals []

/-- Expose only the outer invocation; recursive invocations remain abstract for contracts. -/
def body (relations : Bool := false) (iterRel : Option Expr := none)
    (withColumns : Bool := false) : TacticM Unit := do
  let rules ← if relations then subtypeSimpSet else simpSet
  let rules := if relations then
    { rules with lemmas := rules.lemmas.filter (fun n => !(``Ctx.transpose).isPrefixOf n) ++
        #[``checkedTypePure, ``orElseAssoc, ``unmatchOrElse, ``pureOrElse, ``errorOrElse,
          ``bindOrElse, ``haveOrElse, ``transposeEmptyRows, ``List.mapM_map] }
    else rules
  -- This slot emits `↓` rules, before the generic assignment equations unfold.
  let procedures := if withColumns then rules.procs.push ``iterPremListColumns
    else if relations then rules.procs.push ``iterPremListNoOutputs else rules.procs
  let s ← prepareSimpSet { rules with procs := procedures.push ``assignVar }
  let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel, Outs] at *)))
  evalTactic (← `(tactic| apply Realizes.ofAdd 1))
  let mut names : Array Name := #[]
  for f in invocations do names := names ++ (← eqnsOf f).toArray
  evalTactic (← simpSyntax names #[])
  step s 300 relations iterRel
  unless (← getGoals).isEmpty do throwError "realize_al: goals remain"

/-- Construct the body witness in a generated partial-correctness induction step. -/
elab "realize_step " run:ident : tactic => withoutRecover do
  evalTactic (← `(tactic| apply Realizes.outcome (hq := $run) ))
  body

/-- Construct a recursive body witness with the relation-premise and subtype preset, for
relations and for functions with subtype or structural rules. -/
elab "realize_step" "(" "relations" ")" run:ident : tactic => withoutRecover do
  evalTactic (← `(tactic| apply Realizes.outcome (hq := $run)))
  body true

/-- Construct recursive witnesses through source premises with encoded output columns. -/
elab "realize_step" "(" "columns" ")" run:ident : tactic => withoutRecover do
  evalTactic (← `(tactic| apply Realizes.outcome (hq := $run)))
  body true none true

/-- Construct a recursive body witness with the relation preset and a checked relation for
pattern traversals. -/
elab "realize_step" "(" "relations" ")" "(" "iteration" ":=" relation:term ")" run:ident :
    tactic => withoutRecover do
  evalTactic (← `(tactic| apply Realizes.outcome (hq := $run)))
  let relation ← withMainContext do Term.elabTerm relation none
  body true (some relation)

/-- Prove a nonrecursive reverse certificate by actual quotation reduction. -/
elab "realize_al" : tactic => withoutRecover do
  introNamed
  let (_, _, generated) ← goalParts
  unless generated.isAppOfArity ``ExceptT.mk 4 do
    throwError "realize_al: generated computation is not ExceptT.mk"
  let call := generated.getArg! 3
  let .const name _ := call.getAppFn | throwError "realize_al: expected defined function"
  evalTactic (← `(tactic| unfold $(mkIdent name):ident))
  body

/-- Prove a reverse certificate with an explicit relation for traversal intermediates. -/
elab "realize_al" "(" "iteration" ":=" relation:term ")" : tactic => withoutRecover do
  introNamed
  let relation ← withMainContext do Term.elabTerm relation none
  let (_, _, generated) ← goalParts
  unless generated.isAppOfArity ``ExceptT.mk 4 do
    throwError "realize_al: generated computation is not ExceptT.mk"
  let call := generated.getArg! 3
  let .const name _ := call.getAppFn | throwError "realize_al: expected defined function"
  evalTactic (← `(tactic| unfold $(mkIdent name):ident))
  body false (some relation)

/-- Reverse execution with exact outer subtype checks and generated encoding bridges. -/
elab "realize_al" "(" "subtypes" ")" : tactic => withoutRecover do
  introNamed
  let (_, _, generated) ← goalParts
  unless generated.isAppOfArity ``ExceptT.mk 4 do
    throwError "realize_al: generated computation is not ExceptT.mk"
  let call := generated.getArg! 3
  let .const name _ := call.getAppFn | throwError "realize_al: expected defined function"
  evalTactic (← `(tactic| unfold $(mkIdent name):ident))
  body true

/-- Reverse execution with the subtype preset and a checked relation for pattern traversals. -/
elab "realize_al" "(" "subtypes" ")" "(" "iteration" ":=" relation:term ")" : tactic =>
    withoutRecover do
  introNamed
  let relation ← withMainContext do Term.elabTerm relation none
  let (_, _, generated) ← goalParts
  unless generated.isAppOfArity ``ExceptT.mk 4 do
    throwError "realize_al: generated computation is not ExceptT.mk"
  let call := generated.getArg! 3
  let .const name _ := call.getAppFn | throwError "realize_al: expected defined function"
  evalTactic (← `(tactic| unfold $(mkIdent name):ident))
  body true (some relation)

/-- Reverse execution through source list premises with separately encoded output columns. -/
elab "realize_al" "(" "columns" ")" : tactic => withoutRecover do
  introNamed
  let (_, _, generated) ← goalParts
  unless generated.isAppOfArity ``ExceptT.mk 4 do
    throwError "realize_al: generated computation is not ExceptT.mk"
  let call := generated.getArg! 3
  let .const name _ := call.getAppFn | throwError "realize_al: expected defined function"
  evalTactic (← `(tactic| unfold $(mkIdent name):ident))
  body true none true

/-- Prove one joint induction case, selecting its actual defined-outcome equation. -/
def inductionCase (withColumns : Bool := false) : TacticM Unit := do
  introNamed
  let equation ← withMainContext do
    for d in ← getLCtx do
      if let some (_, _, rhs) := (← instantiateMVars d.type).consumeMData.eq? then
        if rhs.consumeMData.isAppOfArity ``Option.some 2 then return d.userName
    throwError "realize_al: induction case has no defined-outcome equation"
  evalTactic (← `(tactic| apply Realizes.outcome (hq := $(mkIdent equation):ident)))
  body true none withColumns

/-- Prove all members of a recursive group without assuming logical determinism. -/
elab "realize_group " p:ident : tactic => withoutRecover do
  let principle ← realizeGlobalConstNoOverloadWithInfo p
  proveOutcomeGroup principle (inductionCase)

/-- Prove a recursive group whose members bind source list premises with output columns. -/
elab "realize_group" "(" "columns" ")" p:ident : tactic => withoutRecover do
  let principle ← realizeGlobalConstNoOverloadWithInfo p
  proveOutcomeGroup principle (inductionCase true)

end P4SpecTec.Tactic.Realize
