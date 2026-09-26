import P4SpecTec.Tactic.Refine
import P4SpecTec.Refine.StateNormalize

/-!
Bounded exact-state refinement automation for scalar generated functions.
The driver shares value/context normalization with `refine_al`, but every
sequencing and choice step uses the all-outcome stateful calculus.
-/

namespace P4SpecTec.Tactic.StateRefine

open Lean Meta Elab Tactic
open P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Interp_al

/-- The stateful refinement goal without unfolding its observational contract. -/
def refinement : TacticM (Expr × Expr × Expr) := do
  let ty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  unless ty.isAppOfArity ``StateRefines 5 do
    throwError "state_refine_al: not a state refinement goal: {ty}"
  pure (ty.getArg! 2, (ty.getArg! 3).consumeMData, (ty.getArg! 4).consumeMData)

/-- Extend shared scalar normalization with state-preserving equations. -/
def stateSimpSet : TacticM SimpSet := do
  let s ← simpSet
  pure { s with lemmas := s.lemmas ++ #[``liftState, ``liftStatePure, ``liftStateThrow,
    ``liftStateBind, ``orElseState, ``hOrElseState, ``stateDivergeBind, ``stateThrowBind,
    ``stateOrElseUnmatch, ``stateOrElseUnmatchRight, ``stateMkRun, ``stateRunEta,
    ``tracedStateEq, ``checkFuncInputsStateOff,
    ``checkFuncOutputStateOff] }

/-- Unfold only the generated entry, leaving callees available for modular proofs. -/
def unfoldGenerated : TacticM Unit := do
  let (_, _, n) ← refinement
  let call := if n.isAppOfArity ``ExceptT.mk 4 then n.getArg! 3 else n
  if let .const c _ := call.getAppFn then
    evalTactic (← `(tactic| unfold $(mkIdent c):ident))

mutual

/-- Prove all current subgoals independently with the same normalization set. -/
partial def allSteps (s : SimpSet) : TacticM Unit := do
  let goals ← getGoals
  for g in goals do
    setGoals [g]
    step s
    unless ← g.isAssigned do throwError "state_refine_al: a branch remains unproved"

/-- Normalize and apply a state-sensitive calculus step, failing on unsupported heads. -/
partial def step (s : SimpSet) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let _ ← normalize s
  if (← getGoals).isEmpty then return
  normalizeFacts s
  expose
  if (← getGoals).isEmpty then return
  if ← tryTac (evalTactic (← `(tactic| assumption))) then return
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  if ty.isForall then
    introNamed
    let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel, Outs] at *)))
    return ← step s
  let (_, m, n) ← refinement
  if ← tableFacts (← libOf) then return ← step s
  let head := chainHead m
  if ← tryTac (evalTactic (← `(tactic| exact stateRefinesDiverge _))) then return
  if n.isAppOfArity ``letFun 4 then
    evalTactic (← `(tactic| apply stateRefinesHave; intro rf_x rf_h; subst rf_x))
    return ← step s
  if m.isAppOfArity ``StateEval.orElse 3 then
    evalTactic (← `(tactic| apply stateRefinesOrElse))
    return ← allSteps s
  -- Calls retain their fuel abstraction: no success-only observation is used.
  if invocations.any (head.isAppOf ·) then
    let generated := chainHead n
    let call := if generated.isAppOfArity ``ExceptT.mk 4 then generated.getArg! 3
      else generated
    let some c := calleeOf call
      | throwError "state_refine_al: no generated callee at {generated}"
    let theoremName := c.1 ++ `state_refines
    if (← getEnv).contains theoremName then
      if (chainTail m).isSome then
        evalTactic (← `(tactic| apply stateRefinesBind (P := Rel)))
        let goals ← getGoals
        setGoals [goals.head!]
        evalTactic (← `(tactic| apply $(mkIdent theoremName):ident))
        for g in ← getGoals do
          setGoals [g]
          unless ← tryTac (evalTactic (← `(tactic| assumption))) do proveValue s
        setGoals goals.tail!
        return ← allSteps s
      else
        evalTactic (← `(tactic| apply $(mkIdent theoremName):ident))
        for g in ← getGoals do
          setGoals [g]
          unless ← tryTac (evalTactic (← `(tactic| assumption))) do proveValue s
        return
    else throwError "state_refine_al: no all-outcome state refinement theorem {theoremName}"
  let fuelHead := if head.isAppOfArity ``StateEval.liftEval 2 then head.getArg! 1 else head
  if let some f ← (← getMainGoal).withContext (stuckFuel fuelHead) then
    let fn ← (← getMainGoal).withContext do pure (← f.getDecl).userName
    evalTactic (← `(tactic| cases $(mkIdent fn):ident))
    return ← allSteps s
  if head.isAppOfArity ``Pure.pure 4 && (chainTail m).isNone then
    evalTactic (← `(tactic| apply stateRefinesPure))
    return ← proveValue s
  if head.isAppOfArity ``throw 5 && (chainTail m).isNone then
    evalTactic (← `(tactic| exact stateRefinesThrow _ _))
    return
  if let some f ← stuckOn head then
    let fn ← (← getMainGoal).withContext do pure (← f.getDecl).userName
    evalTactic (← `(tactic| cases $(mkIdent fn):ident))
    return ← allSteps s
  if head.isAppOfArity ``ite 5 then
    let condition ← (← getMainGoal).withContext do Term.exprToSyntax (head.getArg! 1)
    let h ← freshName "rf_c"
    evalTactic (← `(tactic| by_cases $(mkIdent h):ident : $condition:term))
    return ← allSteps s
  throwError "state_refine_al: unsupported interpreter head {head}\nagainst {chainHead n}"

end

/-- Entry invocation is unfolded once; inner calls use proved contracts. -/
def prove : TacticM Unit := do
  introNamed
  unfoldGenerated
  let s ← stateSimpSet
  let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel] at *)))
  let (_, m, _) ← refinement
  let some f ← (← getMainGoal).withContext (stuckFuel m)
    | throwError "state_refine_al: expected an interpreter invocation"
  let fn ← (← getMainGoal).withContext do pure (← f.getDecl).userName
  evalTactic (← `(tactic| cases $(mkIdent fn):ident))
  let goals ← getGoals
  for g in goals do
    setGoals [g]
    evalTactic (← `(tactic| simp only [Interp.invoke_func]))
    step s
  unless (← getGoals).isEmpty do throwError "state_refine_al: goals left open"

/-- Prove supported exact-state interpreter refinements without recovery. -/
elab "state_refine_al" : tactic => withoutRecover prove

end P4SpecTec.Tactic.StateRefine
