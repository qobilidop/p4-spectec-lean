import Lean.Elab.Tactic.Split
import Lean.Elab.Tactic.Omega.Frontend
import P4SpecTec.Tactic.Refine.Context

/-!
Forward lockstep refinement: callee theorem pairing, value and equality proofs,
and the refine_al driver. Each proof step retains its explicit SimpSet input;
the public tactic selects the forward preset once and rejects error recovery.
-/

namespace P4SpecTec.Tactic

open Lean Elab Tactic Meta
open P4SpecTec.Refine
open P4SpecTec.Interp_al

/-! ## The callee step -/

/-- The name of the definition a generated call refers to, and whether it
is a relation: `Lib.R.run` gives `R`, `Lib.«$f»` gives `$f`. -/
def calleeOf (e : Expr) : Option (Name × Bool) :=
  match e.consumeMData.getAppFn.consumeMData with
  | .const (.str (.str lib r) "run") _ => some (.str lib r, true)
  | .const c@(.str _ _) _ => some (c, false)
  | _ => none

/-- The induction hypothesis of the recursion group, if any: a hypothesis
`∀ m, m < fuel → ...`. -/
def groupIH : TacticM (Option Name) := do
  (← getMainGoal).withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if let .forallE _ d b _ := ty then
        if d.isConstOf ``Nat then
          if let .forallE _ lt _ _ := b then
            if lt.consumeMData.isAppOfArity ``LT.lt 4 then return some decl.userName
    pure none

/-- The conjunct of a group statement that is about the definition `d`:
its index, by the constant named in each conjunct's generated side. -/
def conjunctIndex (stmt : Expr) (d : Name) : MetaM (Option Nat) := do
  let parts := conjuncts stmt
  let rec mentions (e : Expr) : Bool :=
    match e with
    | .const c _ => c == d
    | .app f a => mentions f || mentions a
    | .lam _ t b _ | .forallE _ t b _ => mentions t || mentions b
    | .letE _ t v b _ => mentions t || mentions v || mentions b
    | .mdata _ e => mentions e
    | .proj _ _ e => mentions e
    | _ => false
  pure (parts.findIdx? mentions)

/-- Pair the interpreter's invocation at the head of `m` with the generated
call at the head of `n`: the callee's refinement theorem, or the induction
hypothesis when the callee is in the group. Leaves the value goals and the
continuation. -/
def calleeStep (s : SimpSet) (m n : Expr) : TacticM Unit := timed "callee" do
  let head := chainHead m
  -- a tail call on both sides is the callee's theorem itself; a generated
  -- call without continuation against an interpreter chain is one
  -- followed by `pure`
  let tail := (chainTail m).isNone
  let n ← if (chainTail n).isNone && !tail then do
      evalTactic (← `(tactic| refine refines_of_bind_pure ?_))
      let some (_, _, n') ← refinesGoal | throwError "refine_al: no goal"
      pure n'
    else pure n
  let genHead := chainHead n
  unless genHead.isAppOfArity ``ExceptT.mk 4 do
    throwError "refine_al: the interpreter invokes a definition but the generated code does not:\
      {indentExpr genHead}"
  let call := (genHead.getArg! 3).consumeMData
  let some (callee, _) := calleeOf call | throwError "refine_al: unknown callee {call}"
  let thm := Name.str callee "refines"
  let some fuel ← fuelArgument? head
    | throwError "refine_al: interpreter invocation has no explicit natural fuel parameter"
  -- the callee proof, as a term applied to the fuel and the goal's arguments
  let ih? ← groupIH
  let mut viaIH := false
  let mut proof : Option Term := none
  if let some ih := ih? then
    let ihTy ← (← getMainGoal).withContext do
      instantiateMVars (← (← fvarOf ih).getType)
    -- `∀ m, m < fuel → (A ∧ B ∧ ...)`
    let body := match ihTy with
      | .forallE _ _ (.forallE _ _ b _) _ => b
      | _ => ihTy
    if let some k ← conjunctIndex body call.getAppFn.constName! then
      let n := (conjuncts body).length
      let fuelStx ← Term.exprToSyntax fuel
      let mut t : Term ← `(($(mkIdent ih) $fuelStx (by omega)))
      for _ in List.range k do t ← `(($t).2)
      if k < n - 1 then t ← `(($t).1)
      proof := some t
      viaIH := true
  if proof.isNone then
    unless (← getEnv).contains thm do
      throwError "refine_al: no refinement theorem {thm} for the callee"
    proof := some (mkIdent thm)
  let some p := proof | unreachable!
  traceStep m!"callee {callee} {if viaIH then "by the induction hypothesis" else "by its theorem"}"
  let mut contGoal? : Option MVarId := none
  noteAction "callee: apply"
  if tail then
    evalTactic (← `(tactic| apply $p))
  else
    -- `refines_bind (callee ...) (fun a b h => ...)`
    -- `apply`, not `refine`: the intermediate relation is found by unification
    evalTactic (← `(tactic| apply refines_bind))
    let goals ← (← getGoals).filterM fun g => do pure !(← g.isAssigned)
    let typed ← goals.mapM fun g => do
      pure (g, (← g.withContext do instantiateMVars (← g.getType)).consumeMData)
    let some (calleeGoal, _) := typed.find? fun (_, t) => t.isAppOfArity ``Refines 5
      | throwError "refine_al: no callee goal"
    let some (contGoal, _) := typed.find? fun (_, t) => t.isForall
      | throwError "refine_al: no cont goal"
    contGoal? := some contGoal
    setGoals [calleeGoal]
    evalTactic (← `(tactic| apply $p))
  -- the remaining goals: the guard, the tables, and the value relations
  noteAction "callee: hypotheses"
  let rest ← getGoals
  let mut valueGoals : List MVarId := []
  for g in rest do
    if ← g.isAssigned then continue
    setGoals [g]
    let ty ← g.withContext do instantiateMVars (← g.getType)
    if ty.consumeMData.isAppOfArity ``Rel 4 then
      valueGoals := valueGoals ++ [g]
    else
      unless ← tryTac (evalTactic (← `(tactic| assumption))) do
        let _ ← normalize s
        unless (← getGoals).isEmpty do
          unless ← tryTac (evalTactic (← `(tactic| assumption))) do
            throwError "refine_al: cannot discharge a hypothesis of the callee:\
              {Lean.MessageData.ofGoal g}"
  setGoals (valueGoals ++ contGoal?.toList)

/-! ## The value prover -/

/-- Prove that an interpreter value is related to a generated value, or
that two canonical lists agree, by computing `canon` on both sides with
the facts. -/
def proveValue (s : SimpSet) : TacticM Unit := timed "proveValue" do
  let goal ← getMainGoal
  let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel, Outs])))
  if (← getGoals).isEmpty then return
  let _ ← normalize s
  if (← getGoals).isEmpty then return
  if ← tryTac (evalTactic (← `(tactic| rfl))) then return
  if ← tryTac (evalTactic (← `(tactic| assumption))) then return
  throwError "refine_al: values not related:{Lean.MessageData.ofGoal (← getMainGoal)}\
    \n(from{Lean.MessageData.ofGoal goal})"

/-- The goals that are not the refinement goal (the holes of a `have`),
and the refinement goal. -/
def holesAndMain : TacticM (List MVarId × List MVarId) := do
  let goals ← getGoals
  let typed ← goals.mapM fun g => do
    pure (g, (← g.withContext do instantiateMVars (← g.getType)).consumeMData)
  let (mains, holes) := typed.partition fun (_, t) => t.isAppOfArity ``Refines 5
  pure (holes.map (·.1), mains.map (·.1))

/-! ## Equality tests -/

/-- The `Value.eq` applications inside `e`, in order. -/
partial def valueEqs (e : Expr) : List Expr :=
  let e := e.consumeMData
  let here := if e.isAppOfArity ``P4SpecTec.Runtime.Value.eq 2 then [e] else []
  here ++ (match e with
    | .app f a => valueEqs f ++ valueEqs a
    | .lam _ t b _ | .forallE _ t b _ => valueEqs t ++ valueEqs b
    | .letE _ t v b _ => valueEqs t ++ valueEqs v ++ valueEqs b
    | .mdata _ e => valueEqs e
    | .proj _ _ e => valueEqs e
    | _ => [])

/-- When the interpreter's condition `c` and the generated condition test
values for equality, rewrite the interpreter's tests into the generated
ones (`eq_of_canon`, arguments related by the value prover). Returns the
condition to split on. -/
def alignEqualities (s : SimpSet) (c : Expr) : TacticM Expr := do
  let some (_, m, n) ← refinesGoal | pure c
  let gh := chainHead n
  let c' := if gh.isAppOfArity ``ite 5 then (gh.getArg! 1).consumeMData else c
  let interp := valueEqs (if (chainHead m).isAppOfArity ``ite 5 then (chainHead m).getArg! 1 else c)
  let gen := if c == c' then [] else valueEqs c'
  traceStep m!"align {interp.length} interpreter tests with {gen.length} generated"
  if interp.length != gen.length || interp.isEmpty then
    -- no counterpart: decide the interpreter's tests on their canonical
    -- values, which compute once both are literals
    for a in interp do
      let h ← freshName "rf_eq"
      let a1 ← (← getMainGoal).withContext do Term.exprToSyntax (a.getArg! 0)
      let a2 ← (← getMainGoal).withContext do Term.exprToSyntax (a.getArg! 1)
      let decided ← tryTac (evalTactic (← `(tactic| have $(mkIdent h):ident :
        P4SpecTec.Runtime.Value.eq $a1 $a2 = true :=
          eq_true_of_canon (by simp only [Rel] at *; rfl))))
      let decided ← if decided then pure true else do
        let ok ← tryTac (evalTactic (← `(tactic| have $(mkIdent h):ident :
          P4SpecTec.Runtime.Value.eq $a1 $a2 = true := eq_true_of_canon ?_)))
        if ok then
          let goals ← getGoals
          let (holes, mains) ← holesAndMain
          setGoals holes
          if ← tryTac (proveValue s) then
            setGoals mains
            pure true
          else
            setGoals goals
            pure false
        else pure false
      let decided ← if decided then pure true else do
        let ok ← tryTac (evalTactic (← `(tactic| have $(mkIdent h):ident :
          P4SpecTec.Runtime.Value.eq $a1 $a2 = false := eq_false_of_canon ?_)))
        if ok then
          let goals ← getGoals
          let (holes, mains) ← holesAndMain
          setGoals holes
          let closed ← tryTac (do
            let _ ← tryTac (evalTactic (← `(tactic| intro rf_ne)))
            let _ ← normalizeAt s `rf_ne
            unless (← getGoals).isEmpty do throwError "not decided")
          if closed then
            setGoals mains
            pure true
          else
            setGoals goals
            pure false
        else pure false
      if decided then
        traceStep m!"decided {a}"
        let _ ← tryTac (evalTactic (← `(tactic| simp only [$(mkIdent h):ident])))
    let some (_, m', _) ← refinesGoal | return c
    let h' := chainHead m'
    return (if h'.isAppOfArity ``ite 5 then (h'.getArg! 1).consumeMData else c)
  for (a, b) in interp.zip gen do
    let h ← freshName "rf_eq"
    let a1 ← (← getMainGoal).withContext do Term.exprToSyntax (a.getArg! 0)
    let a2 ← (← getMainGoal).withContext do Term.exprToSyntax (a.getArg! 1)
    let b1 ← (← getMainGoal).withContext do Term.exprToSyntax (b.getArg! 0)
    let b2 ← (← getMainGoal).withContext do Term.exprToSyntax (b.getArg! 1)
    evalTactic (← `(tactic| have $(mkIdent h):ident :
      P4SpecTec.Runtime.Value.eq $a1 $a2 = P4SpecTec.Runtime.Value.eq $b1 $b2 :=
      eq_of_canon ?_ ?_))
    let (holes, mains) ← holesAndMain
    for g in holes do
      setGoals [g]
      proveValue s
    setGoals mains
    let _ ← tryTac (evalTactic (← `(tactic| simp only [$(mkIdent h):ident])))
  let some (_, m', _) ← refinesGoal | pure c
  let h' := chainHead m'
  pure (if h'.isAppOfArity ``ite 5 then (h'.getArg! 1).consumeMData else c')

/-! ## The driver -/

mutual

/-- One step on the main goal; `true` when the goal was closed or split
into goals the loop continues on. -/
partial def step (s : SimpSet) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let _ ← normalize s
  if (← getGoals).isEmpty then return
  normalizeFacts s
  if (← getGoals).isEmpty then return
  expose
  if (← getGoals).isEmpty then return
  if ← tryTac (evalTactic (← `(tactic| contradiction))) then return
  let goal ← getMainGoal
  try stepCore s goal
  catch e =>
    let msg := e.toMessageData
    if ((← msg.toString).splitOn "during ").length > 1 then throw e
    let ty ← goal.withContext do instantiateMVars (← goal.getType)
    let head := if ty.isAppOfArity ``Refines 5 then chainHead (ty.getArg! 3) else ty
    let gen := if ty.isAppOfArity ``Refines 5 then chainHead (ty.getArg! 4) else ty
    goal.withContext do throwError "{msg}\nduring {← phaseNow.get}, at the interpreter step\
      {indentExpr head}\nagainst the generated{indentExpr gen}"

/-- The step proper, on `goal`. -/
partial def stepCore (s : SimpSet) (goal : MVarId) : TacticM Unit := do
  let ty ← goal.withContext do whnfR (← instantiateMVars (← goal.getType))
  -- binders
  if ty.consumeMData.isForall then
    let n ← goal.withContext do
      match ty.consumeMData with
      | .forallE bn _ _ _ => pure bn
      | _ => pure `rf_x
    let n := if n.isAnonymous || n.hasMacroScopes then `rf_x else n
    let n ← if (← goal.withContext do pure ((← getLCtx).findFromUserName? n).isSome)
      then freshName n.toString else pure n
    evalTactic (← `(tactic| intro $(mkIdent n):ident))
    let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel, Outs] at $(mkIdent n):ident)))
    let _ ← tryTac (evalTactic (← `(tactic| dsimp only at $(mkIdent n):ident)))
    let _ ← normalizeAt s n
    expose
    return ← step s
  let some (_, m, n) ← refinesGoal
    | throwError "refine_al: not a refinement goal:{Lean.MessageData.ofGoal goal}"
  -- table entries the interpreter looks up
  if ← tableFacts (← libOf) then
    let _ ← normalize s
    return ← step s
  let head := chainHead m
  -- divergence
  if head.isAppOfArity ``P4SpecTec.Prelude.Eval.diverge 1 then
    traceStep m!"diverge; interpreter side is{indentExpr m}"
    evalTactic (← `(tactic| exact refines_diverge))
    return
  -- a generated `have`
  if n.isAppOfArity ``letFun 4 then
    let f := (n.getArg! 3).consumeMData
    let x := match f with | .lam bn _ _ _ => bn | _ => `rf_x
    let x ← if (← goal.withContext do pure ((← getLCtx).findFromUserName? x).isSome)
      then freshName x.toString else pure x
    let hx ← freshName s!"h{x}"
    noteAction "have"
    traceStep m!"have {x}"
    evalTactic (← `(tactic| refine refines_have fun $(mkIdent x):ident $(mkIdent hx):ident => ?_))
    return ← step s
  -- sequential choice, before any fuel inside the alternatives is split:
  -- a split there would copy the whole proof into a zero branch that
  -- does not diverge
  if m.isAppOfArity ``P4SpecTec.Prelude.Eval.orElse 3 then
    unless n.isAppOfArity ``P4SpecTec.Prelude.Eval.orElse 3 do
      throwError "refine_al: the interpreter chooses but the generated code does not:\
        {Lean.MessageData.ofGoal goal}"
    noteAction "orElse"
    traceStep "orElse"
    evalTactic (← `(tactic| refine refines_orElse ?_ ?_))
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      step s
    return
  -- the fuel
  if let some f ← goal.withContext (stuckFuel head) then
    let fn ← goal.withContext do pure (← f.getDecl).userName
    noteAction "fuel"
    traceStep m!"fuel {fn}"
    let f' ← freshName fn.toString
    -- anonymous holes: a named hole would refer to an earlier goal of that name
    timed "fuel" (evalTactic (← `(tactic| cases $(mkIdent fn):ident with
      | zero => ?_
      | succ $(mkIdent f'):ident => ?_)))
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let _ ← normalize s
      if (← getGoals).isEmpty then continue
      step s
    return
  -- a pure result
  if head.isAppOfArity ``Pure.pure 4 && (chainTail m).isNone then
    unless n.isAppOfArity ``Pure.pure 4 do
      throwError "refine_al: the interpreter succeeds but the generated code does not:\
        {Lean.MessageData.ofGoal goal}"
    noteAction "pure"
    traceStep "pure"
    evalTactic (← `(tactic| refine refines_pure ?_))
    proveValue s
    return
  -- a failure
  if head.isAppOfArity ``throw 5 && (chainTail m).isNone then
    noteAction "throw"
    traceStep "throw"
    unless ← tryTac (evalTactic (← `(tactic| exact refines_throw))) do
      throwError "refine_al: the interpreter fails but the generated code does not fail alike:\
        {Lean.MessageData.ofGoal goal}"
    return
  -- an invocation
  if invocations.any (head.isAppOf ·) then
    noteAction "callee"
    let tail := (chainTail m).isNone
    calleeStep s m n
    let goals ← getGoals
    let valueGoals := if tail then goals else goals.dropLast
    noteAction "callee: values"
    for g in valueGoals do
      setGoals [g]
      proveValue s
    if tail then
      setGoals []
      return
    setGoals [goals.getLast!]
    return ← step s
  -- the generated side: a match or `if` on a variable, or on a projection
  -- of a variable of a generated structure (destructured first, so that
  -- the projection computes)
  if let some d ← goal.withContext do
      (do
        let gh := chainHead n
        let discrs ← if let some app ← matchMatcherApp? gh then pure app.discrs
          else if gh.isAppOfArity ``ite 5 then pure #[gh.getArg! 1]
          else pure #[]
        -- every match inside the head, outermost first
        let mut inner : Array Expr := #[]
        let mut todo : List Expr := [gh]
        let mut fuel := 10000
        while fuel > 0 do
          fuel := fuel - 1
          match todo with
          | [] => break
          | e :: rest =>
            todo := rest
            let e := e.consumeMData
            if let some app ← matchMatcherApp? e then inner := inner ++ app.discrs
            match e with
            | .app f a => todo := f :: a :: todo
            | .lam _ _ b _ | .forallE _ _ b _ => todo := b :: todo
            | .letE _ _ v b _ => todo := v :: b :: todo
            | .proj _ _ x => todo := x :: todo
            | _ => pure ()
        let lib ← libOf
        let direct ← (discrs ++ inner).filterMapM fun d => do
          match d.consumeMData with
          | .fvar f => if ← isGeneratedVar lib f then pure (some f) else pure none
          | _ => pure none
        if let some f := direct[0]? then
          pure (some f)
        else
          let lib ← libOf
          let mut found : Option FVarId := none
          for d in discrs do
            let ((), st) ← ((← instantiateMVars d).collectFVars).run {}
            for f in st.fvarIds do
              if found.isSome then break
              if ← isGeneratedVar lib f then
                -- a structure of the library: one constructor, no branching
                let ty ← whnfR (← f.getType)
                if let .const c _ := ty.getAppFn then
                  if lib.isPrefixOf c then
                    if let some (.inductInfo info) := (← getEnv).find? c then
                      if info.ctors.length == 1 then found := some f
          pure found) then
    let dn ← goal.withContext do pure (← d.getDecl).userName
    noteAction "cases generated"
    traceStep m!"cases {dn} (generated)"
    timed "cases" (evalTactic (← `(tactic| cases $(mkIdent dn):ident)))
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      noteAction "cases generated: facts"
      normalizeFacts s
      noteAction "cases generated: expose"
      expose
      noteAction "cases generated: normalize"
      let _ ← normalize s
      if (← getGoals).isEmpty then continue
      noteAction "cases generated: step"
      step s
    return
  -- the interpreter side: stuck on a value whose generated counterpart is a variable
  if let some g ← stuckOn head then
    let gn ← goal.withContext do pure (← g.getDecl).userName
    noteAction "cases interpreter"
    traceStep m!"cases {gn} (interpreter)"
    timed "cases" (evalTactic (← `(tactic| cases $(mkIdent gn):ident)))
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      normalizeFacts s
      expose
      let _ ← normalize s
      if (← getGoals).isEmpty then continue
      step s
    return
  -- an `if` on a boolean term on either side
  let cond? : Option Expr :=
    if head.isAppOfArity ``ite 5 then some (head.getArg! 1)
    else
      let gh := chainHead n
      if gh.isAppOfArity ``ite 5 then some (gh.getArg! 1) else none
  if let some c := cond? then
    -- the generated condition, when both sides test: align equality tests
    let c ← alignEqualities s c
    noteAction "split"
    traceStep m!"split on {c}"
    let hc ← freshName "rf_c"
    -- a condition `b = true` splits on the boolean `b`; a proposition by cases
    let b? : Option Expr := match c.consumeMData.eq? with
      | some (_, l, r) =>
        if r.consumeMData.isConstOf ``Bool.true || r.consumeMData.isConstOf ``Bool.false then some l
        else if l.consumeMData.isConstOf ``Bool.true || l.consumeMData.isConstOf ``Bool.false then
          some r
        else none
      | none => none
    let ok ← match b? with
      | some b => do
        let bs ← goal.withContext do Term.exprToSyntax b
        tryTac (evalTactic (← `(tactic| cases $(mkIdent hc):ident : $bs:term)))
      | none => do
        let cs ← goal.withContext do Term.exprToSyntax c
        tryTac (evalTactic (← `(tactic| by_cases $(mkIdent hc):ident : $cs:term)))
    -- a condition that occurs in a dependent position: `split` instead
    unless ok do
      unless ← tryTac (evalTactic (← `(tactic| split))) do
        throwError "refine_al: cannot split on {c}"
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      -- the split's hypothesis decides the condition wherever it occurs
      let _ ← tryTac (evalTactic (← `(tactic| simp only [$(mkIdent hc):ident])))
      if (← getGoals).isEmpty then continue
      let _ ← normalize s
      if (← getGoals).isEmpty then continue
      step s
    return
  -- a generated match on a compound discriminant
  if let some _ ← goal.withContext do matchMatcherApp? (chainHead n) then
    noteAction "split generated match"
    traceStep "split (generated match)"
    if ← tryTac (evalTactic (← `(tactic| split))) then
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        let _ ← tryTac (evalTactic (← `(tactic| subst_vars)))
        normalizeFacts s
        expose
        let _ ← normalize s
        if (← getGoals).isEmpty then continue
        step s
      return
  goal.withContext do
    throwError "refine_al: stuck at the interpreter step{indentExpr head}\nagainst the generated\
      {indentExpr (chainHead n)}\nin{Lean.MessageData.ofGoal goal}"

end

/-- The tactic's body. -/
def refineAl (s : SimpSet) : TacticM Unit := do
  -- the generated definition, unfolded once
  noteAction "entry: intro"
  introNamed
  let goal ← getMainGoal
  goal.withContext do
    let ty := (← instantiateMVars (← goal.getType)).consumeMData
    if ty.isAppOfArity ``Refines 5 then
      let n := (ty.getArg! 4).consumeMData
      if n.isAppOfArity ``ExceptT.mk 4 then
        let call := (n.getArg! 3).consumeMData
        if let .const c _ := call.getAppFn.consumeMData then
          evalTactic (← `(tactic| unfold $(mkIdent c):ident))
  noteAction "entry: Rel"
  let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel] at *)))
  let _ ← normalize s
  -- the invocation the theorem is about: one fuel level, then its body
  noteAction "entry: fuel"
  let some (_, m, _) ← refinesGoal | throwError "refine_al: not a refinement goal"
  let some f ← (← getMainGoal).withContext (stuckFuel m)
    | throwError "refine_al: the interpreter side is not an invocation"
  let fn ← (← getMainGoal).withContext do pure (← f.getDecl).userName
  let f' ← freshName fn.toString
  let mut invEqns : Array Name := #[]
  for i in invocations do invEqns := invEqns ++ (← eqnsOf i).toArray
  let args ← invEqns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let all : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems args
  evalTactic (← `(tactic| cases $(mkIdent fn):ident with
    | zero => (simp only [$all,*]; exact refines_diverge)
    | succ $(mkIdent f'):ident => ?_))
  noteAction "entry: unfold the invocation"
  let _ ← tryTac (evalTactic (← `(tactic| simp only [$all,*])))
  let _ ← normalize s
  expose
  let _ ← normalize s
  phaseTimes.set []
  noteAction "entry: step"
  try step s
  finally traceStep m!"phase times (ms): {← phaseTimes.get}"
  unless (← getGoals).isEmpty do throwError "refine_al: goals left open"

/-- The tactic: see the module docstring. -/
elab "refine_al" : tactic => do
  let s ← simpSet
  -- no error recovery: a failing step must fail the proof, not admit a goal
  try withoutRecover do refineAl (← prepareSimpSet s)
  catch e =>
    throwError "{e.toMessageData}\n(last action: {← phaseNow.get})"

end P4SpecTec.Tactic
