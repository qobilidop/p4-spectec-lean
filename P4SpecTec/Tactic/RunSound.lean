import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Split
import Lean.Elab.Tactic.RCases
import Lean.Elab.Tactic.Rfl
import P4SpecTec.Prelude.Eval

/-!
The tactic `run_sound` that discharges the generated run-soundness
theorems (`R.run i = some (.ok o) → R i o`; design section 4.1). It is a
symbolic execution of the run function's body against the `Prop`
encoding: the hypothesis stating that the `do` block succeeded is
destructured statement by statement with the `Eval.run_*` lemmas, every
`match` on a pattern is split, every call of a group member is turned
into its relation by the induction hypothesis `partial_fixpoint`
provides, an iterated premise's `List.mapM` is turned into a pointwise
fact along the zip, and the goal is closed by the constructor of the rule
path the execution followed, its hypotheses found by assumption.

The tactic is generic: it knows nothing but the shapes `Prelude/Eval.lean`
and the code generator fix, so a rule path the tactic cannot close fails
the build, which is what makes the generated theorem a check.
-/

namespace P4SpecTec.Tactic

open Lean Elab Tactic Meta

/-- Run a tactic, restoring the state and returning `false` on failure. -/
def tryTac (tac : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try
    tac
    pure true
  catch _ =>
    s.restore
    pure false

/-- A fresh accessible hypothesis name with the given prefix. -/
def freshName (pre : String) : TacticM Name := do
  let lctx ← (← getMainGoal).withContext getLCtx
  for i in [0:100000] do
    let n := Name.mkSimple s!"{pre}{i}"
    if (lctx.findFromUserName? n).isNone then return n
  throwError "run_sound: no fresh name"

/-- The type of a local hypothesis, instantiated. -/
def typeOf (h : FVarId) : TacticM Expr := do
  (← getMainGoal).withContext do instantiateMVars (← h.getType)

/-- The local hypothesis named `n`. -/
def fvarOf (n : Name) : TacticM FVarId := do
  (← getMainGoal).withContext do
    match (← getLCtx).findFromUserName? n with
    | some d => pure d.fvarId
    | none => throwError "run_sound: no hypothesis {n}"

/-- Whether `e` is `some (Except.ok _)`. -/
def isSomeOk (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isAppOfArity ``Option.some 2 && (e.getArg! 1).consumeMData.isAppOfArity ``Except.ok 3

/-- The symbolic-execution simp set, at a hypothesis. -/
def simpAt (h : Name) : TacticM Unit := do
  let i := mkIdent h
  evalTactic (← `(tactic| simp only [P4SpecTec.Prelude.Eval.run_hOrElse_ok,
    P4SpecTec.Prelude.Eval.run_orElse_ok, P4SpecTec.Prelude.Eval.run_bind_ok,
    P4SpecTec.Prelude.Eval.run_pure_ok, P4SpecTec.Prelude.Eval.run_check_ok,
    P4SpecTec.Prelude.Eval.run_throw_ok, P4SpecTec.Prelude.Eval.run_mk,
    P4SpecTec.Prelude.Eval.run_err_ok, P4SpecTec.Prelude.Eval.run_unmatch_ok,
    P4SpecTec.Prelude.Eval.run_notHold_ok, Bool.false_eq_true, Bool.true_eq_false,
    Prod.mk.injEq, exists_const, exists_false, and_false, false_and, false_or, or_false,
    and_true, true_and, exists_and_left, exists_and_right, exists_eq_left, exists_eq_right,
    exists_eq_left', exists_eq_right', Option.some.injEq, Except.ok.injEq, Except.error.injEq,
    reduceCtorEq] at $i:ident))

/-- The induction hypothesis for the local function `f`, if any: a
hypothesis `∀ args r, f args = some r → ...`, with the number of binders
before the equation. -/
def ihFor (f : FVarId) : TacticM (Option (Name × Nat)) := do
  (← getMainGoal).withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      let rec scan (t : Expr) (n : Nat) : Option Nat :=
        match t with
        | .forallE _ d b _ =>
          match d.consumeMData.eq? with
          | some (_, lhs, _) =>
            if lhs.consumeMData.getAppFn.consumeMData == .fvar f then some n else scan b (n + 1)
          | none => scan b (n + 1)
        | _ => none
      if let some n := scan ty 0 then return some (decl.userName, n)
    pure none

/-- The run-soundness theorem of a relation whose run function is the
constant `c` (`R.run` gives `R.run_sound`), with the number of explicit
binders before its equation hypothesis, if it exists. -/
def soundnessFor (c : Name) : TacticM (Option (Name × Nat)) := do
  let .str pre "run" := c | pure none
  let thm := Name.str pre "run_sound"
  match (← getEnv).find? thm with
  | some info =>
    let rec scan (t : Expr) (n : Nat) : Option Nat :=
      match t with
      | .forallE _ d b bi =>
        if d.consumeMData.eq?.isSome then some n
        else scan b (if bi.isExplicit then n + 1 else n)
      | _ => none
    pure ((scan info.type 0).map fun n => (thm, n))
  | none => pure none

/-- The goals of a list that are still open. -/
def openGoals (gs : List MVarId) : TacticM (List MVarId) :=
  gs.filterM fun g => do pure !(← g.isAssigned)

/-- A `split` on a pattern over a single-constructor type leaves an equation
on a projection of a variable (`p.1 = C a`), which `subst` cannot use;
destructure every such variable, so that the projection reduces. -/
def projCases : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let goal ← getMainGoal
  let env ← getEnv
  let vars ← goal.withContext do
    let mut out : Array Name := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if let some (_, lhs, rhs) := ty.eq? then
        for side in [lhs.consumeMData, rhs.consumeMData] do
          -- a primitive projection, or a structure's projection function
          let x? : Option Expr := match side with
            | .proj _ _ x => some x
            | .app f x =>
              match f.getAppFn.consumeMData with
              | .const c _ => if (env.getProjectionFnInfo? c).isSome then some x else none
              | _ => none
            | _ => none
          if let some x := x? then
            if let .fvar f := x.consumeMData then
              let d ← f.getDecl
              unless out.contains d.userName do out := out.push d.userName
    pure out
  for v in vars do
    let _ ← tryTac (evalTactic (← `(tactic| cases $(mkIdent v):ident)))
  unless vars.isEmpty do
    let _ ← tryTac (evalTactic (← `(tactic| dsimp only at *)))

/-- Symbolically execute the hypotheses in `work` on the main goal. Every
goal this leaves has been executed to its terminal facts. -/
partial def execute (work : List Name) : TacticM Unit := do
  match work with
  | [] => pure ()
  | h :: rest =>
    if (← getGoals).isEmpty then return
    let hid ← fvarOf h
    let ty ← typeOf hid
    let ty := (← (← getMainGoal).withContext (whnfR ty)).consumeMData
    if ty.isAppOfArity ``Exists 2 then
      let x ← freshName "rs_x"
      let h' ← freshName "rs_h"
      evalTactic (← `(tactic|
        obtain ⟨$(mkIdent x):ident, $(mkIdent h'):ident⟩ := $(mkIdent h):ident))
      execute (h' :: rest)
    else if ty.isAppOfArity ``And 2 then
      let h1 ← freshName "rs_h"
      let h2 := Name.mkSimple s!"{h1}a"
      evalTactic (← `(tactic|
        obtain ⟨$(mkIdent h1):ident, $(mkIdent h2):ident⟩ := $(mkIdent h):ident))
      execute (h1 :: h2 :: rest)
    else if ty.isAppOfArity ``Or 2 then
      let h1 ← freshName "rs_h"
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
      -- a run of a block: normalise, split matches, continue
      if lhs.isAppOf ``ExceptT.run && !isSomeOk rhs then
        -- the record that an earlier alternative did not match: not needed
        execute rest
      else if lhs.isAppOf ``ExceptT.run then
        if ← tryTac (simpAt h) then
          execute (h :: rest)
        else if ← (do
            -- keep the whole equation: a `Prop` hypothesis may state it as is
            let copy ← freshName "rs_c"
            let _ ← tryTac (evalTactic (← `(tactic| have $(mkIdent copy):ident :=
              $(mkIdent h):ident)))
            tryTac (evalTactic (← `(tactic| split at $(mkIdent h):ident)))) then
          let goals ← getGoals
          let mut out := #[]
          for g in goals do
            setGoals [g]
            projCases
            evalTactic (← `(tactic| subst_vars))
            if (← getGoals).isEmpty then continue
            execute (h :: rest)
            out := out ++ (← openGoals (← getGoals)).toArray
          setGoals out.toList
        else
          -- a stuck run (a match on a compound scrutinee): keep as a fact
          execute rest
      else if lhs.getAppFn.consumeMData.isFVar && isSomeOk rhs then
        -- a call of a group member: the induction hypothesis gives the relation
        match ← ihFor lhs.getAppFn.consumeMData.fvarId! with
        | some (ih, n) =>
          let hr ← freshName "rs_r"
          let holes := (List.replicate n (← `(term| _))).toArray
          evalTactic (← `(tactic| have $(mkIdent hr):ident :=
            $(mkIdent ih):ident $holes* $(mkIdent h):ident _ rfl))
          let _ ← tryTac (evalTactic (← `(tactic| dsimp only at $(mkIdent hr):ident)))
          execute rest
        | none => execute rest
      else if lhs.getAppFn.consumeMData.isConst && isSomeOk rhs then
        -- a call of a relation proved earlier: its run-soundness theorem
        match ← soundnessFor lhs.getAppFn.consumeMData.constName! with
        | some (thm, n) =>
          let hr ← freshName "rs_r"
          let holes := (List.replicate n (← `(term| _))).toArray
          let _ ← tryTac (evalTactic (← `(tactic| have $(mkIdent hr):ident :=
            $(mkIdent thm):ident $holes* $(mkIdent h):ident)))
          let _ ← tryTac (evalTactic (← `(tactic| dsimp only at $(mkIdent hr):ident)))
          execute rest
        | none => execute rest
      else if lhs.isFVar || rhs.isFVar then
        if ← tryTac (evalTactic (← `(tactic| subst $(mkIdent h):ident))) then execute rest
        else execute rest
      else
        execute rest
    else
      execute rest

/-- Turn a successful `List.mapM` into its pointwise facts: every hypothesis
`(List.mapM f xs).run = some (.ok ys)` becomes the conjunction
`Eval.run_mapM_ok` gives, then executed. -/
partial def mapMFacts : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let goal ← getMainGoal
  let hyps ← goal.withContext do
    let mut out := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if let some (_, lhs, rhs) := ty.eq? then
        let lhs := lhs.consumeMData
        if lhs.isAppOfArity ``ExceptT.run 4 && (lhs.getArg! 3).consumeMData.isAppOf ``List.mapM &&
            isSomeOk rhs
        then out := out.push decl.userName
    pure out
  for h in hyps do
    let h' ← freshName "rs_m"
    if ← tryTac (evalTactic (← `(tactic| have $(mkIdent h'):ident :=
        P4SpecTec.Prelude.Eval.run_mapM_ok $(mkIdent h):ident))) then
      execute [h']

/-- Introduce every binder of the goal with accessible names. -/
partial def introAll : TacticM (List Name) := do
  let goal ← getMainGoal
  let ty ← goal.withContext (whnfR (← instantiateMVars (← goal.getType)))
  if ty.isForall then
    let n ← freshName "rs_v"
    evalTactic (← `(tactic| intro $(mkIdent n):ident))
    pure (n :: (← introAll))
  else pure []

/-- Instantiate every `∀ x y, (x, y) ∈ l → P` hypothesis with every
membership hypothesis `(u, v) ∈ l` in context, executing the results. -/
partial def useMembership : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let goal ← getMainGoal
  let (alls, mems) ← goal.withContext do
    let mut alls := #[]
    let mut mems := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if ty.isAppOfArity ``Membership.mem 5 then mems := mems.push decl.userName
      else if ty.isForall then
        let isAll ← forallTelescopeReducing ty fun xs _ => do
          if h : xs.size ≥ 3 then
            let last ← inferType xs[xs.size - 1]
            pure (last.isAppOfArity ``Membership.mem 5)
          else pure false
        if isAll then alls := alls.push decl.userName
    pure (alls, mems)
  for hall in alls do
    for hmem in mems do
      let h' ← freshName "rs_e"
      if ← tryTac (evalTactic (← `(tactic| have $(mkIdent h'):ident :=
          $(mkIdent hall):ident _ _ $(mkIdent hmem):ident))) then
        -- beta-reduce the instantiated lambda and execute
        let _ ← tryTac (evalTactic (← `(tactic| simp only [] at $(mkIdent h'):ident)))
        execute [h']
        mapMFacts

/-- Close the goal by a terminal step. -/
partial def closeGoal : TacticM Unit := do
  setGoals (← openGoals (← getGoals))
  if (← getGoals).isEmpty then return
  let goal ← getMainGoal
  try closeGoalCore goal
  catch e =>
    match e with
    | .internal _ _ => throwError "run_sound: internal exception at{Lean.MessageData.ofGoal goal}"
    | _ => throw e
where
  /-- The steps, on the goal `goal`. -/
  closeGoalCore (goal : MVarId) : TacticM Unit := do
    let ty := (← goal.withContext (whnfR (← instantiateMVars (← goal.getType)))).consumeMData
    if ty.isConstOf ``True then
      evalTactic (← `(tactic| trivial))
    else if ← tryTac (evalTactic (← `(tactic| assumption))) then
      pure ()
    else if ty.isForall then
      let _ ← introAll
      evalTactic (← `(tactic| subst_vars))
      if (← getGoals).isEmpty then return
      useMembership
      let goals ← getGoals
      let mut out := #[]
      for g in goals do
        setGoals [g]
        closeGoal
        out := out ++ (← openGoals (← getGoals)).toArray
      setGoals out.toList
    else if ty.isAppOfArity ``Exists 2 then
      -- the witness is assigned by closing the proof goal
      evalTactic (← `(tactic| apply Exists.intro))
      let goals ← getGoals
      for g in goals do
        if ← g.isAssigned then continue
        if ← g.withContext do isProp (← instantiateMVars (← g.getType)) then
          setGoals [g]
          closeGoal
      for g in goals do
        unless ← g.isAssigned do throwError "run_sound: witness not determined"
      setGoals []
    else if ty.isAppOfArity ``And 2 then
      evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
      let goals ← getGoals
      let mut out := #[]
      for g in goals do
        setGoals [g]
        closeGoal
        out := out ++ (← openGoals (← getGoals)).toArray
      setGoals out.toList
    else if ty.eq?.isSome then
      if ← tryTac (evalTactic (← `(tactic| rfl))) then pure ()
      else if ← tryTac (evalTactic (← `(tactic| subst_vars; rfl))) then pure ()
      else if ← tryTac (evalTactic (← `(tactic| simp_all only [Prod.mk.injEq, and_self]))) then
        pure ()
      else throwError "run_sound: cannot close {ty}"
    else if ty.getAppFn.consumeMData.isConst then
      -- an inductive relation: try its constructors in order
      let name := ty.getAppFn.consumeMData.constName!
      match (← getEnv).find? name with
      | some (.inductInfo info) =>
        let mut last : MessageData := ""
        for c in info.ctors do
          let s ← saveState
          try
            let e ← elabTermForApply (mkIdent c)
            liftMetaTactic fun g => g.apply e { newGoals := .all }
            let goals ← getGoals
            -- the hypotheses, in binder order: the generator introduces every
            -- variable in a hypothesis before the hypotheses that use it, so
            -- closing them in order determines the implicit arguments; a data
            -- goal left unassigned fails
            let props ← goals.filterM fun g => do
              if ← g.isAssigned then pure false
              else g.withContext do isProp (← instantiateMVars (← g.getType))
            for g in props do
              if ← g.isAssigned then continue
              setGoals [g]
              closeGoal
              unless (← openGoals (← getGoals)).isEmpty do
                throwError "goal left open:{Lean.MessageData.ofGoal (← getMainGoal)}"
            for g in goals do
              unless ← g.isAssigned do
                throwError "argument not determined:{Lean.MessageData.ofGoal g}"
            setGoals []
            return
          catch e =>
            last := last ++ m!"\n{c}: {e.toMessageData}"
            s.restore
        throwError "run_sound: no constructor of {name} closes the goal\
          {Lean.MessageData.ofGoal goal}\nlast attempt: {last}"
      | _ => throwError "run_sound: cannot close {ty}"
    else
      throwError "run_sound: cannot close {ty}"

/-- Symbolically execute one hypothesis: a step of `run_sound`, for
diagnosing a generated theorem the whole tactic cannot close. -/
elab "run_sound_execute" h:ident : tactic => execute [h.getId]

/-- Close the goal: the last step of `run_sound`, for diagnosis. -/
elab "run_sound_close" : tactic => do
  mapMFacts
  closeGoal

/-- The tactic: see the module docstring. -/
elab "run_sound" : tactic => do
  let _ ← introAll
  let goal ← getMainGoal
  let gty ← goal.withContext (whnfR (← instantiateMVars (← goal.getType)))
  if gty.isConstOf ``True then
    evalTactic (← `(tactic| trivial))
    return
  evalTactic (← `(tactic| subst_vars))
  -- the hypothesis that the run succeeded: the last `_ = some (.ok _)`
  let main ← (← getMainGoal).withContext do
    let mut found : Option (Name × Expr) := none
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if let some (_, lhs, rhs) := ty.eq? then
        if isSomeOk rhs then found := some (decl.userName, lhs.consumeMData)
    pure found
  let some (h, lhs) := main | throwError "run_sound: no hypothesis `_ = some (.ok _)`"
  -- a plain definition: unfold it first
  unless lhs.isAppOf ``ExceptT.run do
    if lhs.getAppFn.isConst then
      let c := lhs.getAppFn.constName!
      evalTactic (← `(tactic| unfold $(mkIdent c):ident at $(mkIdent h):ident))
  execute [h]
  let goals ← getGoals
  let mut out := #[]
  for g in goals do
    setGoals [g]
    mapMFacts
    let gs ← getGoals
    for g' in gs do
      setGoals [g']
      closeGoal
      out := out ++ (← getGoals).toArray
  setGoals out.toList

/-- The conjuncts of a right-nested conjunction. -/
partial def conjuncts (e : Expr) : List Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then e.getArg! 0 :: conjuncts (e.getArg! 1) else [e]

/-- The function constant a `partial_correctness` conjunct is about: the
head of the left-hand side of its first equation. -/
partial def conjunctFunction (e : Expr) : Option Name :=
  match e.consumeMData with
  | .forallE _ d b _ =>
    match d.consumeMData.eq? with
    | some (_, lhs, _) =>
      match lhs.consumeMData.getAppFn.consumeMData with
      | .const n _ => some n
      | _ => conjunctFunction b
    | none => conjunctFunction b
  | _ => none

/-- Prove a conjunction of run-soundness statements, one per member of a
recursion group, with the group's `partial_correctness` principle
`p`: the principle's conjunction lists the members in Lean's order,
which the generator cannot know, so the goal's conjuncts are matched to
the principle's by their function, proved in the principle's order, and
reassembled. Every principle case is closed by `run_sound`. -/
elab "run_sound_group " p:ident : tactic => do
  let principle ← realizeGlobalConstNoOverloadWithInfo p
  let info ← getConstInfo principle
  -- the principle's conclusion follows the fixed parameters of the group
  -- (instances such as `Externs`), n motives (the binders whose types end
  -- in `Prop`) and n cases
  let rec endsInProp : Expr → Bool
    | .forallE _ _ b _ => endsInProp b
    | .sort u => u.isZero
    | _ => false
  let rec fixed (e : Expr) (k : Nat) : Nat :=
    match e with
    | .forallE _ d b _ => if endsInProp d then k else fixed b (k + 1)
    | _ => k
  let rec motives (e : Expr) (n : Nat) : Nat :=
    match e with
    | .forallE _ d b _ => if endsInProp d then motives b (n + 1) else n
    | _ => n
  let rec drop (e : Expr) (k : Nat) : Expr :=
    match k, e with
    | k + 1, .forallE _ _ b _ => drop b k
    | _, e => e
  let k := fixed info.type 0
  let n := motives (drop info.type k) 0
  let leanOrder ← forallBoundedTelescope info.type (some (k + 2 * n)) fun _ body => do
    pure ((conjuncts body).map conjunctFunction)
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let parts := conjuncts target
    let partOf (f : Option Name) : TacticM Expr := do
      match parts.find? fun e => conjunctFunction e == f with
      | some e => pure e
      | none =>
        let shown ← forallBoundedTelescope info.type (some (k + 2 * n)) fun _ body => do
          (conjuncts body).mapM fun e => do pure (← ppExpr e)
        let listed := Lean.MessageData.joinSep (shown.map fun e => m!"\n{e}") ""
        throwError "run_sound_group: no conjunct for {f}; the principle's conjuncts are:{listed}"
    let ordered ← leanOrder.mapM partOf
    let permuted := ordered.dropLast.foldr (fun a acc => mkApp2 (mkConst ``And) a acc)
      ordered.getLast!
    let hm ← mkFreshExprMVar permuted
    setGoals [hm.mvarId!]
    evalTactic (← `(tactic| apply $(mkIdent principle):ident))
    evalTactic (← `(tactic| all_goals run_sound))
    unless (← getGoals).isEmpty do throwError "run_sound_group: cases left open"
    -- reassemble: the k-th conjunct of the goal is a projection of `hm`
    let proj (k : Nat) : MetaM Expr := do
      let mut e := hm
      let n := ordered.length
      for _ in List.range k do e ← mkAppM ``And.right #[e]
      if k < n - 1 then mkAppM ``And.left #[e] else pure e
    let mut proofs : List Expr := []
    for e in parts do
      let f := conjunctFunction e
      let some k := leanOrder.idxOf? f | throwError "run_sound_group: no case for {f}"
      proofs := proofs ++ [← proj k]
    let mut proof := proofs.getLast!
    for a in proofs.dropLast.reverse do
      proof ← mkAppM ``And.intro #[a, proof]
    proof ← instantiateMVars proof
    let ok ← isDefEq (← inferType proof) target
    unless ok do throwError "run_sound_group: reassembled statement does not match"
    goal.assign proof
    setGoals []

end P4SpecTec.Tactic
