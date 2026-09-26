import P4SpecTec.Tactic.RunSound
import P4SpecTec.Refine.StateRules

/-!
Symbolic execution for explicit-state structural run-soundness (not a mirror).
Failure equations are retained as complete rejected-attempt witnesses. This
initial tactic handles structural iteration but does not supply recursive SCC realization.
-/

namespace P4SpecTec.Tactic.StateSound

open Lean Elab Tactic Meta

/-- Whether the observed result is a successful value paired with a final state. -/
def isSomeOk (e : Expr) : Bool :=
  let e := e.consumeMData
  if !e.isAppOfArity ``Option.some 2 then false else
    let pair := (e.getArg! 1).consumeMData
    pair.isAppOfArity ``Prod.mk 4 && (pair.getArg! 2).consumeMData.isAppOfArity ``Except.ok 3

/-- Reduce one successful stateful run without discarding failed-prefix equations. -/
def simpAt (h : Name) : TacticM Unit := do
  let i := mkIdent h
  evalTactic (← `(tactic| simp only [P4SpecTec.Refine.stateRunHOrElseOk,
    P4SpecTec.Refine.stateRunOrElseOk, P4SpecTec.Prelude.StateEval.runBindOk,
    P4SpecTec.Prelude.StateEval.runPure, P4SpecTec.Prelude.StateEval.runThrow,
    P4SpecTec.Refine.stateRunNotHoldOk, P4SpecTec.Refine.stateRunLiftOk,
    P4SpecTec.Refine.stateRunMk, P4SpecTec.Prelude.Eval.run_check_ok,
    P4SpecTec.Prelude.Eval.run_err_ok, P4SpecTec.Prelude.Eval.run_unmatch_ok,
    Bool.false_eq_true, Bool.true_eq_false, Prod.mk.injEq, Option.some.injEq,
    Except.ok.injEq, Except.error.injEq, reduceCtorEq,
    exists_const, exists_false, and_false, false_and, false_or, or_false,
    and_true, true_and, exists_and_left, exists_and_right, exists_eq_left, exists_eq_right,
    exists_eq_left', exists_eq_right'] at $i:ident))

/-- Execute successful state equations, retaining complete failures as structural evidence. -/
partial def execute (work : List Name) : TacticM Unit := do
  match work with
  | [] => pure ()
  | h :: rest =>
    if (← getGoals).isEmpty then return
    let hid ← fvarOf h
    let ty ← typeOf hid
    let ty := (← (← getMainGoal).withContext (whnfR ty)).consumeMData
    if ty.isAppOfArity ``Exists 2 then
      let x ← freshName "ss_x"
      let h' ← freshName "ss_h"
      evalTactic (← `(tactic|
        obtain ⟨$(mkIdent x):ident, $(mkIdent h'):ident⟩ := $(mkIdent h):ident))
      execute (h' :: rest)
    else if ty.isAppOfArity ``And 2 then
      let h1 ← freshName "ss_h"
      let h2 := Name.mkSimple s!"{h1}a"
      evalTactic (← `(tactic|
        obtain ⟨$(mkIdent h1):ident, $(mkIdent h2):ident⟩ := $(mkIdent h):ident))
      execute (h1 :: h2 :: rest)
    else if ty.isAppOfArity ``Or 2 then
      let h1 ← freshName "ss_h"
      evalTactic (← `(tactic|
        rcases $(mkIdent h):ident with $(mkIdent h1):ident | $(mkIdent h1):ident))
      let goals ← getGoals
      let mut out := #[]
      for g in goals do
        setGoals [g]
        execute (h1 :: rest)
        out := out ++ (← getGoals).toArray
      setGoals out.toList
    else if ty.isConstOf ``False then
      evalTactic (← `(tactic| exact absurd $(mkIdent h):ident id))
    else if let some (_, lhs, rhs) := ty.eq? then
      let lhs := lhs.consumeMData
      let rhs := rhs.consumeMData
      if lhs.isAppOf ``P4SpecTec.Prelude.StateEval.run && isSomeOk rhs then
        if ← tryTac (simpAt h) then execute (h :: rest)
        else if ← tryTac (evalTactic (← `(tactic| split at $(mkIdent h):ident))) then
          let goals ← getGoals
          let mut out := #[]
          for g in goals do
            setGoals [g]
            projCases
            let _ ← tryTac (evalTactic (← `(tactic| simp_all only [Prod.mk.injEq])))
            evalTactic (← `(tactic| subst_vars))
            if (← getGoals).isEmpty then continue
            execute (h :: rest)
            out := out ++ (← openGoals (← getGoals)).toArray
          setGoals out.toList
        else execute rest
      else if lhs.getAppFn.consumeMData.isConst && isSomeOk rhs then
        match ← soundnessFor lhs.getAppFn.consumeMData.constName! with
        | some (thm, n) =>
          let hr ← freshName "ss_r"
          let holes := (List.replicate n (← `(term| _))).toArray
          let _ ← tryTac (evalTactic (← `(tactic| have $(mkIdent hr):ident :=
            $(mkIdent thm):ident $holes* $(mkIdent h):ident)))
          execute rest
        | none => execute rest
      else if lhs.isFVar || rhs.isFVar then
        let _ ← tryTac (evalTactic (← `(tactic| subst $(mkIdent h):ident)))
        execute rest
      else execute rest
    else execute rest

/-- Close structural goals, deriving ordered iteration from the actual map's trace. -/
partial def closeStateGoal : TacticM Unit := closeGoalWith do
  let goal ← getMainGoal
  let ty ← goal.withContext do instantiateMVars (← goal.getType)
  unless ty.getAppFn.isConstOf ``P4SpecTec.Refine.StateChain do return false
  let observations ← goal.withContext do
    let mut result := []
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if let some (_, lhs, rhs) := ty.eq? then
        if lhs.isAppOf ``P4SpecTec.Prelude.StateEval.run && isSomeOk rhs then
          result := result ++ [decl.userName]
    pure result
  for h in observations do
    let saved ← saveState
    try
      evalTactic (← `(tactic| refine P4SpecTec.Refine.StateChain.ofRunWithContext
        _ ?_ $(mkIdent h):ident))
      let introduced ← introAll
      let some step := introduced.getLast? | throwError "state_run_sound: missing map step"
      let _ ← tryTac (evalTactic (← `(tactic| simp only [] at $(mkIdent step):ident)))
      execute [step]
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        closeStateGoal
        unless (← openGoals (← getGoals)).isEmpty do
          throwError "state_run_sound: map step left open"
      setGoals []
      return true
    catch _ => saved.restore
  return false

/-- Prove a stateful successful-rule theorem by exact symbolic execution. -/
elab "state_run_sound" : tactic => withoutRecover do
  let _ ← introAll
  evalTactic (← `(tactic| subst_vars))
  let main ← (← getMainGoal).withContext do
    let mut found : Option (Name × Expr) := none
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if let some (_, lhs, rhs) := ty.eq? then
        if isSomeOk rhs then found := some (decl.userName, lhs.consumeMData)
    pure found
  let some (h, lhs) := main | throwError "state_run_sound: no successful paired outcome"
  unless lhs.isAppOf ``P4SpecTec.Prelude.StateEval.run do
    if lhs.getAppFn.isConst then
      evalTactic (← `(tactic| unfold $(mkIdent lhs.getAppFn.constName!):ident
        at $(mkIdent h):ident))
  execute [h]
  let goals ← getGoals
  let mut out := #[]
  for g in goals do
    setGoals [g]
    closeStateGoal
    out := out ++ (← openGoals (← getGoals)).toArray
  setGoals out.toList

end P4SpecTec.Tactic.StateSound
