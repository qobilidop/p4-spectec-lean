import P4SpecTec.Tactic.Refine
import P4SpecTec.Refine.RealizeFuel
import P4SpecTec.Refine.RealizeInterp

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
  evalTactic (← `(tactic| simp only [Nat.add_assoc]))
  calleeFuel
  unless generated.isAppOfArity ``ExceptT.mk 4 do
    throwError "realize_al: expected generated callee, got {generated}"
  let call := (generated.getArg! 3).consumeMData
  match call.getAppFn.consumeMData with
  | .fvar _ =>
    let args ← call.getAppArgs.mapM fun a => Term.exprToSyntax a
    let q ← freshName "rz_q"
    let hq ← freshName "rz_hq"
    evalTactic (← `(tactic| intro $(mkIdent q):ident $(mkIdent hq):ident))
    evalTactic (← `(tactic| apply $(mkIdent `ih):ident $args*
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
    return ← tryTac (evalTactic (← `(tactic| cases $(mkIdent name):ident)))
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
def alignTests (s : SimpSet) (source generated : Expr) : TacticM Bool := do
  let tests := (valueEqs source).eraseDups
  let counterparts := (valueEqs generated).eraseDups
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
  return false

/-- Introduce one accessible binder, preserving representation equalities as facts. -/
def introOne (s : SimpSet) : TacticM Unit := do
  let g ← getMainGoal
  let ty ← g.withContext do whnfR (← g.getType)
  let .forallE name _ _ _ := ty | throwError "realize_al: expected binder"
  let name ← freshName (if name.isAnonymous then "rz_x" else name.toString)
  evalTactic (← `(tactic| intro $(mkIdent name):ident))
  let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel, Outs] at $(mkIdent name):ident)))
  let _ ← normalizeAt s name
  pure ()

/-- Compose one reverse step, retaining the local fuel offset in the reference family. -/
partial def step (s : SimpSet) (remaining : Nat := 300) : TacticM Unit := do
  pruneSolvedGoals
  if (← getGoals).isEmpty then return
  withMainContext do
    if remaining == 0 then throwError "realize_al: symbolic step limit reached"
    let _ ← normalize s
    if (← getGoals).isEmpty then return
    normalizeFacts s
    if (← getGoals).isEmpty then return
    let beforeExpose ← getGoals
    expose
    if (← getGoals).isEmpty then return
    -- Newly exposed constructors must reduce before selecting another discriminant.
    if (← getGoals) != beforeExpose then return ← step s (remaining - 1)
    if ← tryTac (evalTactic (← `(tactic| contradiction))) then return
    let ty ← withMainContext do instantiateMVars (← (← getMainGoal).getType)
    if ty.isForall then
      introOne s
      return ← step s (remaining - 1)
    if ← tableFacts (← libOf) then return ← step s (remaining - 1)
    let (_, reference, generated) ← goalParts
    withMainContext <| withLocalDeclD `rz_fuel (mkConst ``Nat) fun fuel => do
      let source := (mkApp reference fuel).headBeta.consumeMData
      let head := chainHead source
      let genHead := chainHead generated
      traceStep m!"reverse {remaining}: {head.getAppFn} / {genHead.getAppFn}"
      if generated.isAppOfArity ``letFun 4 then
        evalTactic (← `(tactic| apply Realizes.have))
      else if source.isAppOfArity ``Eval.orElse 3 then
        unless generated.isAppOfArity ``Eval.orElse 3 do
          throwError "realize_al: ordered-choice shapes differ"
        evalTactic (← `(tactic| apply Realizes.orElse))
      else if head.isAppOfArity ``Pure.pure 4 && (chainTail source).isNone then
        evalTactic (← `(tactic| apply Realizes.pure))
        if !(← getGoals).isEmpty then proveValue s
      else if head.isAppOfArity ``throw 5 && (chainTail source).isNone then
        evalTactic (← `(tactic| exact Realizes.error _ _))
      else if invocations.any (head.isAppOf ·) && genHead.isAppOfArity ``ExceptT.mk 4 then
        let saved ← getGoals
        if (chainTail source).isSome then
          try evalTactic (← `(tactic| apply Realizes.bind))
          catch _ =>
            let mut facts : Array MessageData := #[]
            for d in ← getLCtx do
              if d.userName.toString.startsWith "rf_c" then facts := facts.push m!"{d.type}"
            throwError "realize_al: cannot compose generated bind {generated}; conditions {facts}"
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
      else if ← splitData genHead then pure ()
      else if ← splitData head then pure ()
      else
        let cond? := if head.isAppOfArity ``ite 5 then some (head.getArg! 1)
          else if genHead.isAppOfArity ``ite 5 then some (genHead.getArg! 1) else none
        if let some c := cond? then
          if ← alignTests s head genHead then return ← step s (remaining - 1)
          if ← alignTests s genHead genHead then return ← step s (remaining - 1)
          let stx ← Term.exprToSyntax c
          let h ← freshName "rf_c"
          evalTactic (← `(tactic| by_cases $(mkIdent h):ident : $stx:term))
        else if ← tryTac (evalTactic (← `(tactic| split))) then pure ()
        else throwError "realize_al: stuck at {head} against {genHead}"
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        step s (remaining - 1)
      setGoals []

/-- Expose only the outer invocation; recursive invocations remain abstract for contracts. -/
def body : TacticM Unit := do
  let rules ← simpSet
  -- This slot emits `↓` rules, before the generic assignment equations unfold.
  let s ← prepareSimpSet { rules with procs := rules.procs.push ``assignVar }
  let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel, Outs] at *)))
  evalTactic (← `(tactic| apply Realizes.ofAdd 1))
  let mut names : Array Name := #[]
  for f in invocations do names := names ++ (← eqnsOf f).toArray
  evalTactic (← simpSyntax names #[])
  step s
  unless (← getGoals).isEmpty do throwError "realize_al: goals remain"

/-- Construct the body witness in a generated partial-correctness induction step. -/
elab "realize_step " run:ident : tactic => withoutRecover do
  evalTactic (← `(tactic| apply Realizes.outcome (hq := $run) ))
  body

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

end P4SpecTec.Tactic.Realize
