import P4SpecTec.Tactic.RunSound
import P4SpecTec.Refine.StateRules
import P4SpecTec.Refine.Fixpoint
import P4SpecTec.Tactic.Monotonicity

/-!
Symbolic execution for explicit-state structural run-soundness (not a mirror).
Failure equations are retained as complete rejected-attempt witnesses.

A recursive group is proved by induction over its least fixed point
(`Tactic/StateGroupSound.lean`). Inside a step the recursive calls are approximants, which
this module's execution recognizes by the hypotheses the step records: a successful
relation call has its rule from the kept induction hypothesis; any other outcome an
approximant has is the final function's, because it is below it; and a rejected attempt or
negative premise retained as a run equation moves to the final functions by the
monotonicity solver the definitions were accepted with.
-/

/-- Report the time of each phase of a state run-soundness proof. -/
register_option p4spectec.stateRunSound.timing : Bool := {
  defValue := false
  descr := "report phase times of state run-soundness proofs"
}

namespace P4SpecTec.Tactic.StateSound

open Lean Elab Tactic Meta

/-- Run a phase, reporting its time when the timing option is set. -/
def timed (phase : String) (action : TacticM α) : TacticM α := do
  unless p4spectec.stateRunSound.timing.get (← getOptions) do return ← action
  let start ← IO.monoMsNow
  let result ← action
  logInfo m!"state_run_sound: {phase} {(← IO.monoMsNow) - start} ms"
  pure result

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

/-- The approximants of a fixed-point induction step, from the hypotheses the step records:
each `g ⊑ c` with `g` a local function and `c` the group member it approximates. -/
def approximants : TacticM (List (FVarId × Expr × Expr)) := do
  if (← getGoals).isEmpty then return []
  (← getMainGoal).withContext do
    let mut out := []
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if ty.isAppOfArity ``Lean.Order.PartialOrder.rel 4 then
        if let .fvar g := (ty.getArg! 2).consumeMData then
          out := out ++ [(g, ty.getArg! 3, decl.toExpr)]
    pure out

/-- The kept induction hypothesis about the approximant `g`, if any: a hypothesis
`Kept (∀ args, g args = some _ → ...)`, with the number of binders before the equation. -/
def keptHypothesis (g : FVarId) : TacticM (Option (Name × Nat)) := do
  (← getMainGoal).withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let type := (← instantiateMVars decl.type).consumeMData
      unless type.isAppOfArity ``P4SpecTec.Refine.Kept 1 do continue
      let rec scan (t : Expr) (n : Nat) : Option Nat :=
        match t with
        | .forallE _ d b _ =>
          match d.consumeMData.eq? with
          | some (_, lhs, _) =>
            if lhs.consumeMData.getAppFn.consumeMData == .fvar g then some n else scan b (n + 1)
          | none => scan b (n + 1)
        | _ => none
      if let some n := scan (type.getArg! 0) 0 then return some (decl.userName, n)
    pure none

/-- Move a retained run equation from approximants to the final functions: a rejected
attempt or negative premise is a fact about the computation as written, with approximant
calls, while a rule states it over the group's definitions. The computation is monotone in
each approximant, by the solver the definitions themselves were accepted with, so its
defined outcome is the final computation's. Outside a fixed-point induction step this does
nothing. -/
def transport (consumers : Array Name) (h : Name) : TacticM Unit := do
  let approx ← approximants
  if approx.isEmpty then return
  let hid ← fvarOf h
  let goal ← getMainGoal
  let result ← goal.withContext do
    let ty := (← instantiateMVars (← hid.getType)).consumeMData
    let some (_, lhs, rhs) := ty.eq? | return none
    unless approx.any (fun (g, _, _) => lhs.containsFVar g) do return none
    let mut lhs := lhs
    let mut proof := mkFVar hid
    for (g, c, le) in approx do
      unless lhs.containsFVar g do continue
      let f ← mkLambdaFVars #[mkFVar g] lhs
      -- the approximant's order is its hypothesis's: resolution fails on long function types
      let below := (← instantiateMVars (← inferType le)).consumeMData
      let mono ← mkFreshExprMVar (← mkAppOptM ``Lean.Order.monotone
        #[below.getArg! 0, below.getArg! 1, none, none, f])
      try solveGeneratedMonotonicity consumers mono.mvarId!
      catch e => throwError "state_run_sound: a retained computation is not shown monotone \
        in an approximant: {e.toMessageData}"
      proof ← mkAppM ``P4SpecTec.Refine.flatSome
        #[mkAppN (← instantiateMVars mono) #[mkFVar g, c, le], proof]
      lhs := f.beta #[c]
    pure (some (proof, ← mkEq lhs rhs))
  let some (proof, type) := result | return
  let goal ← (← getMainGoal).assert h type proof
  let (_, goal) ← goal.intro1P
  setGoals [← goal.clear hid]

/-- The prefix of the local definitions that name a relation's attempts. -/
def attemptPrefix : String := "ss_a"

/-- Whether an expression is one of the local definitions naming an attempt. -/
def isAttempt (e : Expr) : MetaM Bool := do
  let .fvar id := e.consumeMData | return false
  let decl ← id.getDecl
  pure (decl.isLet && decl.userName.toString.startsWith attemptPrefix)

/-- The number of attempts rejected on this path: the retained failures of named attempts.
A relation has one constructor per complete attempt, in order, so this is also the index
of the rule the path selects. -/
def rejectedAttempts : TacticM Nat := do
  if (← getGoals).isEmpty then return 0
  (← getMainGoal).withContext do
    let mut count := 0
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let type := (← instantiateMVars decl.type).consumeMData
      let some (_, lhs, _) := type.eq? | continue
      let lhs := lhs.consumeMData
      if lhs.isAppOfArity ``P4SpecTec.Prelude.StateEval.run 3 && (← isAttempt (lhs.getArg! 1)) then
        count := count + 1
    pure count

/-- Name every attempt of the relation being proved as a local definition: `R.«@attemptK»`
applied to the arguments of the run under proof. A later case analysis rewrites these
with the goal, so a rejected alternative is compared with a closed term, once, when it is
retained, and a rule's rejected prefix with a name. -/
def nameAttempts (args : Array Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let relation ← goal.withContext do
    let target ← whnfR (← instantiateMVars (← goal.getType))
    pure target.getAppFn.constName?
  let some relation := relation | return
  let mut current := goal
  let mut index := 0
  repeat
    let candidate := Name.str relation s!"@attempt{index}"
    let some info := (← getEnv).find? candidate | break
    unless info.levelParams.isEmpty do break
    let value := mkAppN (mkConst candidate) args
    let type ← current.withContext do
      unless ← isTypeCorrect value do
        throwError "state_run_sound: {candidate} does not take the run's arguments"
      inferType value
    let (_, next) ← (← current.define (Name.mkSimple s!"{attemptPrefix}{index}") type
      value).intro1P
    current := next
    index := index + 1
  setGoals [current]

/-- Restate a retained rejected alternative as the named attempt it is: the first attempt
of the relation not yet rejected on this path. Returns whether it was one. -/
def foldAttempt (h : Name) : TacticM Bool := do
  let index ← rejectedAttempts
  let goal ← getMainGoal
  let hid ← fvarOf h
  let folded ← goal.withContext do
    let some decl := (← getLCtx).findFromUserName? (Name.mkSimple s!"{attemptPrefix}{index}")
      | return none
    let some value := decl.value? | return none
    let type := (← instantiateMVars (← hid.getType)).consumeMData
    let some (_, lhs, rhs) := type.eq? | return none
    let lhs := lhs.consumeMData
    unless lhs.isAppOfArity ``P4SpecTec.Prelude.StateEval.run 3 do return none
    unless ← isDefEq (lhs.getArg! 1) value do return none
    pure (some (← mkEq (mkAppN lhs.getAppFn #[lhs.getArg! 0, decl.toExpr, lhs.getArg! 2]) rhs))
  match folded with
  | some type =>
    setGoals [← goal.replaceLocalDeclDefEq hid type]
    pure true
  | none => pure false

/-- Keep a retained run equation's computation behind a local definition. Later steps
simplify with every hypothesis: they would rewrite the computation with facts of the
selected path, so that it no longer is the attempt a rule names, and they would traverse
it again at every step. A local definition is opaque to them and transparent to the final
definitional comparison with the rule. -/
def protect (h : Name) : TacticM Unit := do
  let hid ← fvarOf h
  let goal ← getMainGoal
  let parts ← goal.withContext do
    let ty := (← instantiateMVars (← hid.getType)).consumeMData
    let some (_, lhs, rhs) := ty.eq? | return none
    let lhs := lhs.consumeMData
    unless lhs.isAppOfArity ``P4SpecTec.Prelude.StateEval.run 3 do return none
    let computation := lhs.getArg! 1
    if computation.isFVar then return none
    pure (some (computation, ← inferType computation, lhs, rhs))
  let some (computation, type, lhs, rhs) := parts | return
  let name ← freshName "ss_c"
  let goal ← goal.define name type computation
  let (definition, goal) ← goal.intro1P
  let kept ← goal.withContext do
    mkEq (mkAppN lhs.getAppFn #[lhs.getArg! 0, mkFVar definition, lhs.getArg! 2]) rhs
  let goal ← goal.assert h kept (mkFVar hid)
  let (_, goal) ← goal.intro1P
  setGoals [← goal.clear hid]

/-- Split a successful run of alternatives by the rule itself, not by rewriting: the
rejected attempt stays the term the definition has, which is the attempt a rule names.
Returns the hypothesis that replaces `h`. -/
def splitAlternative (h : Name) (lhs : Expr) : TacticM (Option Name) := do
  unless lhs.isAppOfArity ``P4SpecTec.Prelude.StateEval.run 3 do return none
  let computation := (lhs.getArg! 1).consumeMData
  let rule ← if computation.isAppOf ``HOrElse.hOrElse then
      pure (mkIdent ``P4SpecTec.Refine.stateRunHOrElseOk)
    else if computation.isAppOf ``P4SpecTec.Prelude.StateEval.orElse then
      pure (mkIdent ``P4SpecTec.Refine.stateRunOrElseOk)
    else return none
  let split ← freshName "ss_o"
  unless ← tryTac (evalTactic (← `(tactic| have $(mkIdent split):ident :=
      ($rule:ident _ _ _ _ _).mp $(mkIdent h):ident))) do return none
  evalTactic (← `(tactic| clear $(mkIdent h):ident))
  pure (some split)

/-- Execute successful state equations, retaining complete failures as structural evidence. -/
partial def execute (consumers : Array Name) (work : List Name) : TacticM Unit := do
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
      execute consumers (h' :: rest)
    else if ty.isAppOfArity ``And 2 then
      let h1 ← freshName "ss_h"
      let h2 := Name.mkSimple s!"{h1}a"
      evalTactic (← `(tactic|
        obtain ⟨$(mkIdent h1):ident, $(mkIdent h2):ident⟩ := $(mkIdent h):ident))
      execute consumers (h1 :: h2 :: rest)
    else if ty.isAppOfArity ``Or 2 then
      let h1 ← freshName "ss_h"
      evalTactic (← `(tactic|
        rcases $(mkIdent h):ident with $(mkIdent h1):ident | $(mkIdent h1):ident))
      let goals ← getGoals
      let mut out := #[]
      for g in goals do
        setGoals [g]
        execute consumers (h1 :: rest)
        out := out ++ (← getGoals).toArray
      setGoals out.toList
    else if ty.isConstOf ``False then
      evalTactic (← `(tactic| exact absurd $(mkIdent h):ident id))
    else if let some (_, lhs, rhs) := ty.eq? then
      let lhs := lhs.consumeMData
      let rhs := rhs.consumeMData
      if lhs.isAppOf ``P4SpecTec.Prelude.StateEval.run && !isSomeOk rhs then
        -- a failure retained as structural evidence, stated over the final functions
        timed "transport" (transport consumers h)
        unless ← timed "fold" (foldAttempt h) do protect h
        execute consumers rest
      else if lhs.isAppOf ``P4SpecTec.Prelude.StateEval.run then
        if let some split ← splitAlternative h lhs then execute consumers (split :: rest)
        else if ← tryTac (simpAt h) then execute consumers (h :: rest)
        else if ← tryTac (evalTactic (← `(tactic| split at $(mkIdent h):ident))) then
          let goals ← getGoals
          let mut out := #[]
          for g in goals do
            setGoals [g]
            projCases
            -- destructuring may leave several goals: each is normalized and continues the
            -- same work list
            for g' in ← getGoals do
              setGoals [g']
              let _ ← tryTac (evalTactic (← `(tactic| simp_all only [Prod.mk.injEq])))
              if (← getGoals).isEmpty then continue
              evalTactic (← `(tactic| subst_vars))
              execute consumers (h :: rest)
              out := out ++ (← openGoals (← getGoals)).toArray
          setGoals out.toList
        else execute consumers rest
      else if lhs.getAppFn.consumeMData.isFVar && rhs.isAppOfArity ``Option.some 2 then
        -- a call of an approximant inside the induction over the group's fixed point
        let g := lhs.getAppFn.consumeMData.fvarId!
        match ← (if isSomeOk rhs then keptHypothesis g else pure none) with
        | some (ih, n) =>
          -- a successful relation call: the induction hypothesis gives the rule
          let hr ← freshName "ss_r"
          let holes := (List.replicate n (← `(term| _))).toArray
          evalTactic (← `(tactic| have $(mkIdent hr):ident :=
            ($(mkIdent ih):ident).out $holes* $(mkIdent h):ident))
          execute consumers rest
        | none =>
          -- any other outcome is the final function's: the approximant is below it
          if let some (_, final, le) := (← approximants).find? (·.1 == g) then
            let goal ← getMainGoal
            let hid ← fvarOf h
            let (type, proof) ← goal.withContext do
              let args := lhs.getAppArgs
              let proof ← mkAppM ``P4SpecTec.Refine.flatSome #[mkAppN le args, mkFVar hid]
              pure (← mkEq (mkAppN final args) rhs, proof)
            let goal ← goal.assert (← freshName "ss_f") type proof
            let (_, goal) ← goal.intro1P
            setGoals [goal]
          execute consumers rest
      else if lhs.getAppFn.consumeMData.isConst && isSomeOk rhs then
        match ← soundnessFor lhs.getAppFn.consumeMData.constName! with
        | some (thm, n) =>
          let hr ← freshName "ss_r"
          let holes := (List.replicate n (← `(term| _))).toArray
          let _ ← tryTac (evalTactic (← `(tactic| have $(mkIdent hr):ident :=
            $(mkIdent thm):ident $holes* $(mkIdent h):ident)))
          execute consumers rest
        | none => execute consumers rest
      else if lhs.isFVar || rhs.isFVar then
        let _ ← tryTac (evalTactic (← `(tactic| subst $(mkIdent h):ident)))
        execute consumers rest
      else execute consumers rest
    else execute consumers rest

/-- Close a rejected-prefix premise from the retained failures in order, each chosen by
the state it starts at. A constructor search would compare every retained failure with
every attempt, and a comparison of two different attempts is not cheap to refute. -/
partial def closePrefix : TacticM Bool := do
  let goal ← getMainGoal
  let ty ← goal.withContext do instantiateMVars (← goal.getType)
  unless ty.isAppOfArity ``P4SpecTec.Refine.RejectedPrefix 4 do return false
  let attempts ← goal.withContext (whnfR (ty.getArg! 1))
  if attempts.isAppOfArity ``List.nil 1 then
    return ← tryTac (evalTactic (← `(tactic| exact P4SpecTec.Refine.RejectedPrefix.nil _)))
  unless attempts.isAppOfArity ``List.cons 3 do return false
  let start := (ty.getArg! 2).consumeMData
  let candidates ← goal.withContext do
    let mut out := []
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let hypothesis := (← instantiateMVars decl.type).consumeMData
      let some (_, lhs, rhs) := hypothesis.eq? | continue
      let lhs := lhs.consumeMData
      if lhs.isAppOfArity ``P4SpecTec.Prelude.StateEval.run 3 && !isSomeOk rhs &&
          (start.isMVar || (lhs.getArg! 2).consumeMData == start) then
        out := out ++ [decl.userName]
    pure out
  let attempt := attempts.getArg! 1
  let remaining := attempts.getArg! 2
  for h in candidates do
    let saved ← saveState
    try
      let closed ← goal.withContext do
        let hypothesis ← fvarOf h
        let some (_, lhs, rhs) := (← instantiateMVars (← hypothesis.getType)).consumeMData.eq?
          | return false
        -- the outcome `some (.error .unmatch, t)`: only a mismatch is a rejection
        unless rhs.consumeMData.isAppOfArity ``Option.some 2 do return false
        let pair := (rhs.consumeMData.getArg! 1).consumeMData
        unless pair.isAppOfArity ``Prod.mk 4 do return false
        let failure := (pair.getArg! 2).consumeMData
        unless failure.isAppOfArity ``Except.error 3 &&
            (failure.getArg! 2).consumeMData.isConstOf ``P4SpecTec.Prelude.Fail.unmatch do
          return false
        unless ← isDefEq (lhs.consumeMData.getArg! 1) attempt do return false
        let after := pair.getArg! 3
        let tail ← mkFreshExprSyntheticOpaqueMVar (mkApp4 ty.getAppFn (ty.getArg! 0) remaining
          after (ty.getArg! 3))
        let proof := mkAppN (mkConst ``P4SpecTec.Refine.RejectedPrefix.cons
            ty.getAppFn.constLevels!)
          #[ty.getArg! 0, attempt, remaining, start, after, ty.getArg! 3, mkFVar hypothesis, tail]
        goal.assign proof
        setGoals [tail.mvarId!]
        closePrefix
      if closed then return true
    catch _ => pure ()
    saved.restore
  return false

/-- The rule a path selects, for the relation whose attempts are named. -/
def selectedRule (relation : Name) : TacticM (Option Nat) := do
  let named ← (← getMainGoal).withContext do
    let some decl := (← getLCtx).findFromUserName? (Name.mkSimple s!"{attemptPrefix}0")
      | return false
    let some value := decl.value? | return false
    pure (value.getAppFn.constName?.map (·.getPrefix) == some relation)
  if named then pure (some (← rejectedAttempts)) else pure none

/-- Close structural goals, deriving ordered iteration from the actual map's trace. -/
partial def closeStateGoal (consumers : Array Name) : TacticM Unit :=
    closeGoalWith (first := selectedRule) do
  let goal ← getMainGoal
  let ty ← goal.withContext do instantiateMVars (← goal.getType)
  if ty.isAppOfArity ``P4SpecTec.Refine.RejectedPrefix 4 then
    return ← timed "prefix" closePrefix
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
      execute consumers [step]
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        closeStateGoal consumers
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
      -- the attempts take the run's arguments but the state
      nameAttempts (lhs.getAppArgs.extract 0 (lhs.getAppNumArgs - 1))
      evalTactic (← `(tactic| unfold $(mkIdent lhs.getAppFn.constName!):ident
        at $(mkIdent h):ident))
  timed "execution" (execute #[] [h])
  let goals ← getGoals
  let mut out := #[]
  for g in goals do
    setGoals [g]
    timed "rule" (closeStateGoal #[])
    out := out ++ (← openGoals (← getGoals)).toArray
  setGoals out.toList

end P4SpecTec.Tactic.StateSound
