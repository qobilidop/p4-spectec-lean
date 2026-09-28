import Lean.Elab.Tactic.Split
import Lean.Meta.Tactic.Generalize
import Lean.Elab.Tactic.Omega.Frontend
import P4SpecTec.Tactic.Refine.Context
import P4SpecTec.Tactic.Traversal
import P4SpecTec.Tactic.IterationColumns
import P4SpecTec.Refine.RealizeInterp
import P4SpecTec.Refine.RealizeChoice

/-!
Forward lockstep refinement: callee theorem pairing, value and equality proofs,
and the refine_al driver. Each proof step retains its explicit SimpSet input;
the public tactic selects the forward preset once and rejects error recovery.
-/

namespace P4SpecTec.Tactic

open Lean Elab Tactic Meta
open P4SpecTec.Refine
open P4SpecTec.Interp_al

/-- Close the main goal when two hypotheses decide the same Boolean both ways,
`h₁ : e = true` and `h₂ : e = false`. A branch split on an interpreter condition can
repeat an earlier split's condition under a fresh name; the branch is then impossible. -/
def closeBoolConflict : TacticM Bool := do
  let goal ← getMainGoal
  goal.withContext do
    let mut trues : Array (Expr × FVarId) := #[]
    let mut falses : Array (Expr × FVarId) := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if let some (_, lhs, rhs) := ty.eq? then
        if rhs.consumeMData.isConstOf ``Bool.true then trues := trues.push (lhs, decl.fvarId)
        else if rhs.consumeMData.isConstOf ``Bool.false then
          falses := falses.push (lhs, decl.fvarId)
    for (e, t) in trues do
      for (e', f) in falses do
        if e == e' then
          -- `true = false`, refuted by evaluation
          let conflict ← mkEqTrans (← mkEqSymm (.fvar t)) (.fvar f)
          let refuted ← mkDecideProof (mkNot (← mkEq (mkConst ``Bool.true) (mkConst ``Bool.false)))
          goal.assign (← mkAbsurd (← goal.getType) conflict refuted)
          replaceMainGoal []
          return true
    return false

/-- Close the main goal when an equation between constructor applications is refuted by
unification (`ListV (_ :: _) = ListV []`); the attempt is kept only if it closes the goal. -/
def closeConstructorClash : TacticM Bool := do
  let goal ← getMainGoal
  let candidates ← goal.withContext do
    let mut out : Array FVarId := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if let some (_, lhs, rhs) := ty.eq? then
        if (← isConstructorApp lhs) && (← isConstructorApp rhs) then out := out.push decl.fvarId
    pure out
  for f in candidates do
    let closed ← tryTac do
      let subgoals ← (← getMainGoal).cases f
      unless subgoals.isEmpty do throwError "not refuted"
      replaceMainGoal []
    if closed then return true
  return false

/-- Close a branch whose natural or integer inequalities are contradictory, as when one side
checks a slice bound in integers and the other in naturals. `omega` runs only when the context
has such an inequality. -/
def closeArithmetic : TacticM Bool := do
  let arithmetic ← withMainContext do
    (← getLCtx).anyM fun decl => do
      if decl.isImplementationDetail then return false
      let ty := (← instantiateMVars decl.type).consumeMData
      let ty := if ty.isAppOfArity ``Not 1 then (ty.getArg! 0).consumeMData else ty
      unless ty.isAppOfArity ``LT.lt 4 || ty.isAppOfArity ``LE.le 4 do return false
      let carrier := (ty.getArg! 0).consumeMData
      return carrier.isConstOf ``Nat || carrier.isConstOf ``Int
  unless arithmetic do return false
  -- decided Boolean checks (`decide p || decide q = true`) become propositions `omega` reads;
  -- the attempt is atomic, so a failed one leaves the context unchanged
  tryTac do
    let _ ← tryTac (evalTactic (← `(tactic|
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not] at *)))
    evalTactic (← `(tactic| omega))

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

/-- Discharge an actual quoted declaration obligation from source-specification membership.
The resulting proof is checked against the goal's exact global environment. -/
def declarationFromSpec : TacticM Bool := tryTac do
  let goal ← getMainGoal
  let ty ← goal.withContext do instantiateMVars (← goal.getType)
  unless ty.isAppOfArity ``Holds 2 do throwError "not a declaration hypothesis"
  let .const declaration _ := (ty.getArg! 1).consumeMData
    | throwError "not a quoted declaration"
  let some (hspec, spec) ← specHyp | throwError "no source environment hypothesis"
  let proof ← goal.withContext do
    let hs ← fvarOf hspec
    let mem ← memProof spec declaration
    Term.exprToSyntax (mkApp2 (.fvar hs) (mkConst declaration) mem)
  evalTactic (← `(tactic| exact $proof))

/-! ## The value prover -/

/-- The value whose payload a fact `v.it = p` fixes, if `e` is such a fact's left side. -/
def payloadOf? (e : Expr) : Option Expr :=
  match e.consumeMData with
  | .proj ``P4SpecTec.Util.Source.info 0 v => some v
  | e => if e.isAppOfArity ``P4SpecTec.Util.Source.info.it 4 then some (e.getArg! 3) else none

/-- The `Value.eq` tests inside `e`, in order. -/
partial def valueEqTests (e : Expr) : List Expr :=
  let e := e.consumeMData
  let here := if e.isAppOfArity ``P4SpecTec.Runtime.Value.eq 2 then [e] else []
  here ++ (match e with
    | .app f a => valueEqTests f ++ valueEqTests a
    | .lam _ t b _ | .forallE _ t b _ => valueEqTests t ++ valueEqTests b
    | .mdata _ e => valueEqTests e
    | _ => [])

/-- Decide equality tests on values whose payloads the context fixes (`a.it = p`), through
`eq_of_its` and the literal equalities; opaque projections such as `x.fst` need this. -/
def rewriteEqsByPayload : TacticM Bool := withMainContext do
  let mut facts : Array (Expr × FVarId) := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty := (← instantiateMVars decl.type).consumeMData
    if let some (_, lhs, _) := ty.eq? then
      if let some v := payloadOf? lhs then facts := facts.push (v, decl.fvarId)
  if facts.isEmpty then return false
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let mut changed := false
  for test in valueEqTests ty do
    let some (_, fa) := facts.find? (·.1 == test.getArg! 0) | continue
    let some (_, fb) := facts.find? (·.1 == test.getArg! 1) | continue
    let proof ← mkAppM ``eq_of_its #[.fvar fa, .fvar fb]
    let proofSyntax ← Term.exprToSyntax proof
    if ← tryTac (evalTactic (← `(tactic| rw [$proofSyntax:term]))) then changed := true
  return changed

/-- Prove that an interpreter value is related to a generated value, or
that two canonical lists agree, by computing `canon` on both sides with
the facts. -/
partial def proveValue (s : SimpSet) : TacticM Unit := timed "proveValue" do
  let goal ← getMainGoal
  let ty ← goal.withContext do instantiateMVars (← goal.getType)
  if ty.isAppOf ``PairLookupRel then
    evalTactic (← `(tactic| constructor))
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      evalTactic (← `(tactic| refine ⟨_, by rfl, ?_⟩))
      let _ ← normalize s
      unless (← getGoals).isEmpty do
        unless ← tryTac (evalTactic (← `(tactic| assumption))) do
          evalTactic (← `(tactic| rfl))
    return
  let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel, Outs, ColumnRows])))
  if (← getGoals).isEmpty then return
  let _ ← normalize s
  if (← getGoals).isEmpty then return
  if ← tryTac (evalTactic (← `(tactic| rfl))) then return
  if ← tryTac (evalTactic (← `(tactic| assumption))) then return
  if ← tryTac (evalTactic (← `(tactic|
      exact Representation.ValueBEq.elemOfRel (by assumption) (by assumption)))) then return
  -- membership of a represented element in a represented list, each shown separately
  if ← tryTac do
      evalTactic (← `(tactic| refine Representation.ValueBEq.elemOfRel ?_ ?_))
      let [element, list] ← getGoals | throwError "membership premises"
      setGoals [element]
      proveValue s
      unless (← getGoals).isEmpty do throwError "membership element remains"
      setGoals [list]
      unless ← tryTac (evalTactic (← `(tactic| assumption))) do
        evalTactic (← `(tactic| refine Eq.trans (by assumption) ?_))
        proveValue s
      unless (← getGoals).isEmpty do throwError "membership list remains"
    then return
  -- two equality tests of canonically related operands
  if ← tryTac do
      evalTactic (← `(tactic| refine eq_of_canon ?_ ?_))
      for g in ← getGoals do
        setGoals [g]
        unless ← tryTac (evalTactic (← `(tactic| first | assumption | rfl))) do
          let _ ← normalize s
          unless (← getGoals).isEmpty do evalTactic (← `(tactic| first | assumption | rfl))
      unless (← getGoals).isEmpty do throwError "related equality operands remain"
    then return
  if ← tryTac do
      encodingShapes
      if !(← getGoals).isEmpty then
        let _ ← normalize s
        pure ()
      unless (← getGoals).isEmpty do throwError "canonical shape proof remains open"
    then return
  -- two library encoders of the same generated value (a recursive group's nested helper and
  -- the generic instance encoder)
  if ← tryTac do
      encodingCoherence
      unless (← getGoals).isEmpty do throwError "encodings differ"
    then return
  if ← tryTac do
      unless ← rewriteEqsByPayload do throwError "no payload-decided equality"
      let _ ← normalize s
      unless (← getGoals).isEmpty do
        unless ← tryTac (evalTactic (← `(tactic| rfl))) do throwError "payload equality open"
    then return
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

/-- Close the main goal when a decided reference membership `raws.any (Value.eq v) = c`
and a decided generated membership `List.elem x xs = c'` disagree although `v` represents
`x` and `raws` represents `xs` (`ValueBEq.elemOfRel`, both premises by the value prover). -/
def closeMembershipConflict (s : SimpSet) : TacticM Bool := do
  let goal ← getMainGoal
  let (references, generated) ← goal.withContext do
    -- each decided membership with a proof of `test = outcome`; `¬ test = b` decides `!b`
    let mut references : Array (Expr × Expr × Bool) := #[]
    let mut generated : Array (Expr × Expr × Bool) := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      let (ty, negated) := if ty.isAppOfArity ``Not 1 then (ty.getArg! 0, true) else (ty, false)
      let some (_, lhs, rhs) := ty.consumeMData.eq? | continue
      let lhs := lhs.consumeMData
      let outcome := if rhs.consumeMData.isConstOf ``Bool.true then some true
        else if rhs.consumeMData.isConstOf ``Bool.false then some false else none
      let some outcome := outcome | continue
      let flip := if outcome then ``eq_false_of_ne_true else ``eq_true_of_ne_false
      let proof ← if negated then mkAppM flip #[decl.toExpr] else pure decl.toExpr
      let outcome := if negated then !outcome else outcome
      if lhs.isAppOfArity ``List.any 3 &&
          (lhs.getArg! 2).consumeMData.isAppOfArity ``P4SpecTec.Runtime.Value.eq 1 then
        references := references.push (proof, lhs, outcome)
      else if lhs.isAppOfArity ``List.elem 4 then
        generated := generated.push (proof, lhs, outcome)
    pure (references, generated)
  for (r, reference, outcome) in references do
    for (g, member, outcome') in generated do
      if outcome == outcome' then continue
      let saved ← saveState
      let closed ← try
        let (hx, hs) ← goal.withContext do
          let raws := reference.getArg! 1
          let v := (reference.getArg! 2).consumeMData.getArg! 0
          let x := member.getArg! 2
          let xs := member.getArg! 3
          let hx ← mkFreshExprSyntheticOpaqueMVar
            (← mkAppM ``P4SpecTec.Refine.Rel #[v, x])
          let hs ← mkFreshExprSyntheticOpaqueMVar (← mkEq
            (← mkAppM ``P4SpecTec.Refine.canons #[raws])
            (← mkAppM ``P4SpecTec.Refine.canons #[← mkAppM ``List.map
              #[← withLocalDeclD `y (← inferType x) fun y => do
                  mkLambdaFVars #[y] (← mkAppM ``P4SpecTec.Prelude.toValue #[y]), xs]]))
          let same ← mkAppM ``Representation.ValueBEq.elemOfRel #[hx, hs]
          -- `c = raws.any … = xs.elem x = c'` with `c ≠ c'`
          let conflict ← mkEqTrans (← mkEqSymm r) (← mkEqTrans same g)
          let refuted ← mkDecideProof (mkNot (← inferType conflict))
          goal.assign (← mkAbsurd (← goal.getType) conflict refuted)
          pure (hx.mvarId!, hs.mvarId!)
        for hole in [hx, hs] do
          setGoals [hole]
          proveValue s
          unless (← getGoals).isEmpty do throwError "membership premise remains"
        pure true
      catch e =>
        traceStep m!"membership conflict not shown: {e.toMessageData}"
        saved.restore
        pure false
      if closed then return true
  return false

/-- Close the main goal when a decided test `Value.eq a b = false` holds of canonically
equal values (shown by the value prover), or `Value.eq a b = true` of canonically
different ones (refuted by normalization); such a branch is impossible. Proof terms are
built directly, so the closer is independent of the surrounding elaboration scope. -/
def closeValueEqConflict (s : SimpSet) : TacticM Bool := do
  let goal ← getMainGoal
  let tests ← goal.withContext do
    let mut out : Array (FVarId × Expr × Expr × Bool) := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if let some (_, lhs, rhs) := ty.eq? then
        let lhs := lhs.consumeMData
        if lhs.isAppOfArity ``P4SpecTec.Runtime.Value.eq 2 then
          let (a, b) := (lhs.getArg! 0, lhs.getArg! 1)
          if rhs.consumeMData.isConstOf ``Bool.false then out := out.push (decl.fvarId, a, b, false)
          else if rhs.consumeMData.isConstOf ``Bool.true then
            out := out.push (decl.fvarId, a, b, true)
    pure out
  for (f, a, b, outcome) in tests do
    let saved ← saveState
    let closed ← try
      let hole ← goal.withContext do
        let same ← mkEq (← mkAppM ``P4SpecTec.Refine.canon #[a])
          (← mkAppM ``P4SpecTec.Refine.canon #[b])
        let hole ← mkFreshExprSyntheticOpaqueMVar (if outcome then mkNot same else same)
        -- `true = false` from the decided test and its refutation, then absurdity
        let other ← mkAppM (if outcome then ``eq_false_of_canon else ``eq_true_of_canon) #[hole]
        let conflict ← if outcome then mkEqTrans (← mkEqSymm (.fvar f)) other
          else mkEqTrans (← mkEqSymm other) (.fvar f)
        let refuted ← mkDecideProof (mkNot (← mkEq (mkConst ``Bool.true) (mkConst ``Bool.false)))
        goal.assign (← mkAbsurd (← goal.getType) conflict refuted)
        pure hole.mvarId!
      setGoals [hole]
      if outcome then
        evalTactic (← `(tactic| intro $(mkIdent `rf_ne):ident))
        let _ ← normalizeAt s `rf_ne
        -- a remaining constructor clash (`ListV (_ :: _) = ListV []`) closes by unification
        unless (← getGoals).isEmpty do
          evalTactic (← `(tactic| cases $(mkIdent `rf_ne):ident))
      else
        proveValue s
      unless (← getGoals).isEmpty do throwError "not decided"
      pure true
    catch e =>
      traceStep m!"value test conflict not shown: {e.toMessageData}"
      saved.restore
      pure false
    if closed then return true
  closeMembershipConflict s

/-- The list variable of a generated emptiness test, `xs.beq []`, `xs == []` or
`xs.isEmpty`, at the head of `e`'s condition; other conditions are not list tests. -/
def generatedListTest? (e : Expr) : MetaM (Option FVarId) := do
  unless e.isAppOfArity ``ite 5 do return none
  let condition := (← instantiateMVars (e.getArg! 1)).consumeMData
  let some (_, test, _) := condition.eq? | return none
  let test := test.consumeMData
  let emptyTest (list other : Expr) : Option FVarId :=
    if other.consumeMData.isAppOfArity ``List.nil 1 then
      match list.consumeMData with | .fvar f => some f | _ => none
    else none
  -- the empty list may be on either side of the test
  if test.isAppOfArity ``List.beq 4 || test.isAppOfArity ``BEq.beq 4 then
    return (emptyTest (test.getArg! 2) (test.getArg! 3)).orElse
      fun _ => emptyTest (test.getArg! 3) (test.getArg! 2)
  if test.isAppOfArity ``List.isEmpty 2 then
    return match (test.getArg! 1).consumeMData with | .fvar f => some f | _ => none
  return none

/-- A generated list variable at the head of the generated side whose length or literal
position is inspected (`List.length xs`, `Iter.idx xs k`, or `xs[k]?` after unfolding),
as in the bound check and access of a literal index. Splitting it exposes the related
reference list, so both sides decide their checks on constructors. -/
def generatedIndexedList : TacticM (Option FVarId) := withMainContext do
  let some (_, _, n) ← refinesGoal | return none
  let n ← instantiateMVars n
  let head := chainHead n
  let indexed (e : Expr) : Option Expr :=
    let e := e.consumeMData
    if e.isAppOfArity ``P4SpecTec.Prelude.Iter.idx 3 then some (e.getArg! 1)
    else if e.isAppOfArity ``GetElem?.getElem? 8 then some (e.getArg! 6)
    else none
  let inspected (e : Expr) : Option Expr :=
    let e := e.consumeMData
    if e.isAppOfArity ``List.length 2 then some (e.getArg! 1) else indexed e
  -- only a list the generated code actually accesses at a position is split
  let some access := head.find? fun e => (inspected e).any fun list =>
      list.consumeMData.isFVar &&
        (n.find? fun a => (indexed a).any (·.consumeMData == list.consumeMData)).isSome
    | return none
  let some list := inspected access | return none
  let list := list.consumeMData
  unless (← whnfR (← inferType list)).isAppOfArity ``List 1 do return none
  return some list.fvarId!

/-- A generated emptiness test the interpreter already decided on the related value:
split the generated list, so that each branch's related value decides the same test,
and continue with `k`; impossible branches close by their conflicting tests. -/
def splitGeneratedList (s : SimpSet) (n : Expr) (k : TacticM Unit) : TacticM Bool := do
  let goal ← getMainGoal
  let some f ← goal.withContext (generatedListTest? (chainHead n)) | return false
  traceStep m!"cases {← goal.withContext do pure (← f.getDecl).userName} (generated list test)"
  let subgoals ← goal.cases f
  for g in subgoals.map (·.mvarId) do
    setGoals [g]
    normalizeFacts s
    expose
    let _ ← normalize s
    if (← getGoals).isEmpty then continue
    if ← closeBoolConflict then continue
    if ← closeConstructorClash then continue
    if ← closeValueEqConflict s then continue
    k
  return true

/-- The lists a Boolean fact tests for emptiness (`[].beq xs`, `xs.beq []`, `xs.isEmpty`,
also under `&&`), when the list is not yet a constructor. -/
partial def emptinessTests (e : Expr) : List Expr :=
  let e := e.consumeMData
  let open_ (x : Expr) : List Expr :=
    let x := x.consumeMData
    if x.isAppOf ``List.nil || x.isAppOf ``List.cons then [] else [x]
  if e.isAppOfArity ``List.beq 4 || e.isAppOfArity ``BEq.beq 4 then
    let (a, b) := (e.getArg! 2, e.getArg! 3)
    if a.consumeMData.isAppOfArity ``List.nil 1 then open_ b
    else if b.consumeMData.isAppOfArity ``List.nil 1 then open_ a else []
  else if e.isAppOfArity ``List.isEmpty 2 then open_ (e.getArg! 1)
  else if e.isAppOfArity ``and 2 || e.isAppOfArity ``Eq 3 || e.isAppOfArity ``Not 1 then
    e.getAppArgs.toList.flatMap emptinessTests
  else []

/-- A decided fact tests a generated list for emptiness while the list is still symbolic:
split the list, so the fact and the related reference values decide on constructors. -/
def splitFactList (s : SimpSet) (k : TacticM Unit) : TacticM Bool := do
  let goal ← getMainGoal
  let lists ← goal.withContext do
    let mut out : Array Expr := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail || !decl.userName.toString.startsWith "rf_c" then continue
      out := out ++ (emptinessTests (← instantiateMVars decl.type)).toArray
    pure out
  for list in lists do
    let saved ← saveState
    let split ← try
      let listSyntax ← goal.withContext (Term.exprToSyntax list)
      let h ← freshName "rf_c_split"
      evalTactic (← `(tactic| cases $(mkIdent h):ident : $listSyntax:term))
      pure (some h)
    catch _ =>
      saved.restore
      pure none
    let some h := split | continue
    traceStep m!"cases {list} (list tested in a fact)"
    for g in ← getGoals do
      setGoals [g]
      let _ ← tryTac (evalTactic (← `(tactic| simp only [$(mkIdent h):ident] at *)))
      if (← getGoals).isEmpty then continue
      normalizeFacts s
      if (← getGoals).isEmpty then continue
      if ← closeBoolConflict then continue
      if ← closeConstructorClash then continue
      if ← closeValueEqConflict s then continue
      k
    return true
  return false

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
    -- only an impossible branch can pair a call with a generated terminal outcome
    if ← closeBoolConflict then return
    if ← closeConstructorClash then return
    if ← closeValueEqConflict s then return
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
    -- a value relation, also unfolded (an induction hypothesis states `canon v = canon x`)
    let canonical := match ty.consumeMData.eq? with
      | some (_, lhs, rhs) =>
        lhs.isAppOfArity ``P4SpecTec.Refine.canon 1 && rhs.isAppOfArity ``P4SpecTec.Refine.canon 1
      | none => false
    if ty.consumeMData.isAppOfArity ``Rel 4 || canonical then
      valueGoals := valueGoals ++ [g]
    else
      let fromSpec ← declarationFromSpec
      unless fromSpec || (← tryTac (evalTactic (← `(tactic| assumption)))) do
        let _ ← normalize s
        unless (← getGoals).isEmpty do
          unless ← tryTac (evalTactic (← `(tactic| assumption))) do
            throwError "refine_al: cannot discharge a hypothesis of the callee:\
              {Lean.MessageData.ofGoal g}"
  setGoals (valueGoals ++ contGoal?.toList)

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
      -- each attempt is atomic: an undecided attempt leaves no `have` or hole behind
      let decided ← if decided then pure true else tryTac do
        evalTactic (← `(tactic| have $(mkIdent h):ident :
          P4SpecTec.Runtime.Value.eq $a1 $a2 = true := eq_true_of_canon ?_))
        let (holes, mains) ← holesAndMain
        setGoals holes
        proveValue s
        unless (← getGoals).isEmpty do throwError "not decided"
        setGoals mains
      let decided ← if decided then pure true else tryTac do
        evalTactic (← `(tactic| have $(mkIdent h):ident :
          P4SpecTec.Runtime.Value.eq $a1 $a2 = false := eq_false_of_canon ?_))
        let (holes, mains) ← holesAndMain
        setGoals holes
        let _ ← tryTac (evalTactic (← `(tactic| intro $(mkIdent `rf_ne):ident)))
        let _ ← normalizeAt s `rf_ne
        unless (← getGoals).isEmpty do throwError "not decided"
        setGoals mains
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

/-- Pair ordered traversals using checked positional input observations, including zips. -/
def mapMGoals (s : SimpSet) (relation : Expr) (m n : Expr) : TacticM Bool := withMainContext do
  let mh := chainHead m
  let nh := chainHead n
  unless mh.isAppOf ``List.mapM && nh.isAppOf ``List.mapM && (chainTail m).isSome do
    return false
  let some inputs ← columnTraversalInputs (proveValue s) mh.getAppArgs.back! nh.getAppArgs.back!
    | return false
  -- a generated traversal that ends the computation continues with `pure`
  if (chainTail n).isNone then
    evalTactic (← `(tactic| refine refines_of_bind_pure ?_))
  let q ← Term.exprToSyntax relation
  let h ← Term.exprToSyntax inputs
  if (← columnTraversalRelation m n).isSome then
    let inputsSyntax ← Term.exprToSyntax nh.getAppArgs.back!
    evalTactic (← `(tactic|
      apply refines_bind (P := fun outputs results =>
        List.Forall₂ $q outputs results ∧ List.length results = List.length $inputsSyntax)
        (Refines.mapMWithLength $h ?_)))
  else
    evalTactic (← `(tactic|
      apply refines_bind (P := List.Forall₂ $q) (Refines.mapM $h ?_)))
  return true

/-- The closed `List.map` applications inside `e`, outermost first. -/
partial def closedMaps (e : Expr) : List Expr :=
  let e := e.consumeMData
  let here := if e.isAppOfArity ``List.map 4 && !e.hasLooseBVars then [e] else []
  here ++ (match e with
    | .app f a => closedMaps f ++ closedMaps a
    | .lam _ t b _ | .forallE _ t b _ => closedMaps t ++ closedMaps b
    | .letE _ t v b _ => closedMaps t ++ closedMaps v ++ closedMaps b
    | .mdata _ e => closedMaps e
    | .proj _ _ e => closedMaps e
    | _ => [])

/-- Pair a reference traversal producing values (an iterated expression) with a pure
generated `List.map` inside the generated head, when their input lists are positionally
related. The generated side takes no step; the continuation receives the related results. -/
def pureMapTraversal (s : SimpSet) (m n : Expr) : TacticM Bool := withMainContext do
  let mh := chainHead m
  unless mh.isAppOfArity ``List.mapM 6 && (chainTail m).isSome do return false
  unless ← isDefEq (mh.getArg! 3) (mkConst ``P4SpecTec.Lang.Il.value) do return false
  let nh := chainHead n
  if nh.isAppOf ``List.mapM then return false
  -- the map may already be bound by a generated `have` whose defining fact is in context
  let bound ← (← getLCtx).foldlM (init := #[]) fun found decl => do
    if decl.isImplementationDetail then return found
    return found ++ (closedMaps (← instantiateMVars decl.type)).toArray
  for candidate in closedMaps nh ++ closedMaps n ++ bound.toList do
    let saved ← saveState
    try
      let some inputs ← columnTraversalInputs (proveValue s) mh.getAppArgs.back!
          (candidate.getArg! 3) | throwError "unrelated inputs"
      let h ← Term.exprToSyntax inputs
      let c ← Term.exprToSyntax candidate
      let element ← Term.exprToSyntax (candidate.getArg! 1)
      traceStep m!"pure generated map {candidate}"
      evalTactic (← `(tactic|
        apply refines_bind_pure (c := $c)
          (P := List.Forall₂ (@P4SpecTec.Refine.Rel $element _)) (refines_mapM_pureMap $h ?_)))
      return true
    catch _ => saved.restore
  return false

/-- Element-wise traversal results `List.Forall₂ Rel vs xs`: add the canonical list
equality `canons vs = canons (xs.map toValue)` that the value prover uses. -/
def elementResults (n : Name) : TacticM Unit := do
  let pointwise ← withMainContext do
    let some declaration := (← getLCtx).findFromUserName? n | return false
    let type := (← instantiateMVars declaration.type).consumeMData
    return type.isAppOfArity ``List.Forall₂ 5 &&
      (type.getArg! 2).consumeMData.isAppOfArity ``P4SpecTec.Refine.Rel 2
  if pointwise then
    let fact ← freshName "rf_c_elements"
    let added ← tryTac (evalTactic (← `(tactic|
      have $(mkIdent fact):ident := canonsOfForall₂ P4SpecTec.Prelude.toValue $(mkIdent n))))
    traceStep m!"element results {n}: {if added then "canonical list" else "not converted"}"

/-- Whether hypothesis `n` is a batch's positional column relation (possibly with its length
fact), `canons row = canons (encoders.map (· x))`: column collection reads its encoders. -/
def columnRelationHyp (n : Name) : TacticM Bool := withMainContext do
  let some declaration := (← getLCtx).findFromUserName? n | return false
  let type ← whnfR (← instantiateMVars declaration.type)
  let relation := if type.isAppOfArity ``And 2 then (type.getArg! 0).consumeMData else type
  unless relation.isAppOfArity ``List.Forall₂ 5 do return false
  lambdaTelescope (relation.getArg! 2) fun _ body => do
    let some (_, lhs, rhs) := body.consumeMData.eq? | return false
    return lhs.isAppOfArity ``canons 1 && rhs.isAppOfArity ``canons 1 &&
      (rhs.getArg! 0).isAppOfArity ``List.map 4

/-- Execute a concrete reference traversal of checked local lookups.
This entry point is shared by the forward and reverse drivers. -/
def lookupTraversalAt (s : SimpSet) (m : Expr) : TacticM Bool := do
  unless (chainHead m).isAppOf ``List.mapM do return false
  let hypotheses ← (← getMainGoal).withContext do
    let mut names : List Name := []
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      if ty.isAppOfArity ``List.Forall₂ 5 &&
          (ty.getArg! 2).isAppOf ``PairLookupRel then
        names := names ++ [decl.userName]
    pure names
  for h in hypotheses do
    for projection in [``pairLookupLeft, ``pairLookupRight] do
      let vs ← freshName "rf_lookupValues"
      let eq ← freshName "rf_lookupEq"
      let canonEq ← freshName "rf_lookupCanons"
      if ← tryTac (do
          evalTactic (← `(tactic|
            obtain ⟨$(mkIdent vs):ident, $(mkIdent eq):ident, $(mkIdent canonEq):ident⟩ :=
              lookupMapM _ _ ($(mkIdent projection) $(mkIdent h))))
          let _ ← normalizeAt s eq
          evalTactic (← `(tactic| rw [$(mkIdent eq):ident]))) then return true
  return false

/-- Execute checked local lookup traversal in the current forward refinement goal. -/
def lookupTraversal (s : SimpSet) : TacticM Bool := do
  let some (_, m, _) ← refinesGoal | return false
  lookupTraversalAt s m

/-- Find a related generated option, generalizing record projections before shape exposure. -/
def relatedOption : TacticM (Option FVarId) := withMainContext do
  let lib ← libOf
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some (_, lhs, rhs) := (← instantiateMVars d.type).consumeMData.eq? then
      if !lhs.isAppOfArity ``canon' 1 && !lhs.isAppOfArity ``P4SpecTec.Refine.canon 1 then continue
      let rhs := if rhs.isAppOfArity ``P4SpecTec.Util.Source.info.mk 6 then
          rhs.getAppArgs[rhs.getAppArgs.size - 3]! else rhs
      let rhs := if rhs.isAppOfArity ``canon' 1 then rhs.getArg! 0 else rhs
      if !rhs.isAppOfArity ``P4SpecTec.Lang.Il.value'.OptV 1 then continue
      let encoded := (rhs.getArg! 0).consumeMData
      if !encoded.isAppOf ``Option.map then continue
      let receiver := encoded.getAppArgs.back!.consumeMData
      if let .fvar f := receiver then
        if (← whnfR (← f.getType)).isAppOfArity ``Option 1 && (← isGeneratedVar lib f) then
          return some f
      let environment ← getEnv
      let projection := match receiver with
        | .proj .. => true
        | _ => match receiver.getAppFn with
          | .const name _ => (environment.getProjectionFnInfo? name).isSome
          | _ => false
      if projection then
        if !(← whnfR (← inferType receiver)).isAppOfArity ``Option 1 then continue
        let ((), state) ← receiver.collectFVars.run {}
        if !(← state.fvarIds.anyM (fun f => isGeneratedVar lib f)) then continue
        let hyps := (← getLCtx).foldl (init := #[]) fun ids declaration =>
          if declaration.isImplementationDetail then ids else ids.push declaration.fvarId
        let name ← mkFreshUserName `rf_option
        let (_, variables, goal) ← (← getMainGoal).generalizeHyp
          #[{ expr := receiver, xName? := some name }] hyps
        setGoals [goal]
        return variables[0]?
  return none

/-- Decide a generated test and the reference test of the same step together. When the
generated head is `Eval.check t` over one generated variable `p`, and the reference head
branches on a Boolean `b`, prove `b = t` in a small side goal by cases on `p` (each case
computes from the related facts), rewrite, and split on `t` alone. The constructor split then
happens on the side goal's small terms instead of on the whole refinement goal. -/
def alignTest (s : SimpSet) (m n : Expr) : TacticM Bool := withMainContext do
  let gh := chainHead n
  -- `Eval.check t`, or its unfolding `if t = true then pure () else throw .unmatch`
  let t? ← if gh.isAppOfArity ``P4SpecTec.Prelude.Eval.check 1 then pure (some (gh.getArg! 0))
    else if gh.isAppOfArity ``ite 5 then
      match (← instantiateMVars (gh.getArg! 1)).consumeMData.eq? with
      | some (_, t, r) => pure (if r.consumeMData.isConstOf ``Bool.true then some t else none)
      | none => pure none
    else pure none
  let some t := t? | return false
  let t := (← instantiateMVars t).consumeMData
  if t.isConstOf ``Bool.true || t.isConstOf ``Bool.false || t.hasLooseBVars then return false
  let lib ← libOf
  let ((), st) ← t.collectFVars.run {}
  let gens ← st.fvarIds.filterM fun f => (isGeneratedVar lib f : MetaM Bool)
  unless gens.size == 1 do return false
  let p := gens[0]!
  let h := chainHead m
  unless h.isAppOfArity ``ite 5 do return false
  let some (_, b, r) := (← instantiateMVars (h.getArg! 1)).consumeMData.eq? | return false
  unless r.consumeMData.isConstOf ``Bool.true do return false
  if b.hasLooseBVars then return false
  let saved ← saveState
  try
    let goal ← getMainGoal
    let pName ← p.getUserName
    let prop ← mkEq b t
    let side ← mkFreshExprSyntheticOpaqueMVar prop
    setGoals [side.mvarId!]
    evalTactic (← `(tactic| cases $(mkIdent pName):ident))
    for g in ← getGoals do
      setGoals [g]
      normalizeFacts s
      if (← getGoals).isEmpty then continue
      expose
      if (← getGoals).isEmpty then continue
      let _ ← normalize s
      if (← getGoals).isEmpty then continue
      unless ← tryTac (evalTactic (← `(tactic| rfl))) do
        throwError "tests differ:{Lean.MessageData.ofGoal (← getMainGoal)}"
    setGoals [goal]
    let hb ← freshName "rf_test"
    let proof ← instantiateMVars side
    let goal ← goal.assert hb prop proof
    let (_, goal) ← goal.intro1P
    setGoals [goal]
    evalTactic (← `(tactic| simp only [$(mkIdent hb):ident]))
    let hc ← freshName "rf_c"
    let ts ← withMainContext do Term.exprToSyntax t
    evalTactic (← `(tactic| cases $(mkIdent hc):ident : $ts:term))
    traceStep m!"aligned the reference test with the generated test on {pName}"
    return true
  catch e =>
    traceStep m!"test alignment not shown: {e.toMessageData}"
    saved.restore
    return false

/-- The generated variable to split at the generated head: the discriminant of a `match` or
`if` in the head, or of a structure of the library whose projection the head inspects. -/
def generatedDiscriminant (n : Expr) : TacticM (Option FVarId) := withMainContext do
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
    -- a component of a generated pair: destructure the pair first
    | .proj ``Prod _ (.fvar f) => if ← isGeneratedVar lib f then pure (some f) else pure none
    | e =>
      if e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3 then
        match (e.getArg! 2).consumeMData with
        | .fvar f => if ← isGeneratedVar lib f then pure (some f) else pure none
        | _ => pure none
      else pure none
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
    pure found

/-- A generated head still inspecting a generated variable after the reference side reached its
outcome: split that variable, so each branch computes; continue with `k`. -/
def splitGeneratedDiscriminant (s : SimpSet) (n : Expr) (k : TacticM Unit) : TacticM Bool := do
  let some d ← generatedDiscriminant n | return false
  let dn ← withMainContext do pure (← d.getDecl).userName
  traceStep m!"cases {dn} (generated, after the reference outcome)"
  evalTactic (← `(tactic| cases $(mkIdent dn):ident))
  let goals ← getGoals
  for g in goals do
    setGoals [g]
    normalizeFacts s
    expose
    k
  return true

/-- A generated condition left after the reference side reached its outcome (such as a slice
bound check stated in naturals against the reference's integer check): split on it; the
branch contradicting the reference's decided facts closes by `omega`. -/
def splitGeneratedCondition (s : SimpSet) (n : Expr) (k : TacticM Unit) : TacticM Bool := do
  let gh ← instantiateMVars (chainHead n)
  -- the head's first closed condition, such as a bound check inside `Eval.ofOption`
  let some branch := gh.find? fun e =>
      e.isAppOfArity ``ite 5 && !(e.getArg! 1).hasLooseBVars
    | return false
  let condition := branch.getArg! 1
  let hc ← freshName "rf_c"
  let conditionSyntax ← withMainContext do Term.exprToSyntax condition
  unless ← tryTac (evalTactic (← `(tactic|
      by_cases $(mkIdent hc):ident : $conditionSyntax:term))) do
    return false
  traceStep m!"split on the generated condition {condition}"
  for g in ← getGoals do
    setGoals [g]
    let _ ← tryTac (evalTactic (← `(tactic| simp only [$(mkIdent hc):ident])))
    if (← getGoals).isEmpty then continue
    if ← closeArithmetic then continue
    let _ ← normalize s
    if (← getGoals).isEmpty then continue
    k
  return true

/-! ## The driver -/

mutual

/-- Normalize the main goal and dispatch its next refinement step. -/
partial def step (s : SimpSet) (iteration : Option Expr := none)
    (subtypes : Bool := false) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let _ ← normalize s
  if (← getGoals).isEmpty then return
  if subtypes then
    encodingShapes
    if !(← getGoals).isEmpty then encodingLengths
  normalizeFacts s
  if (← getGoals).isEmpty then return
  let beforeExpose ← getGoals
  expose
  if (← getGoals).isEmpty then return
  if subtypes && (← getGoals) != beforeExpose then return ← step s iteration subtypes
  if let some f ← relatedOption then
    let name ← withMainContext do pure (← f.getDecl).userName
    evalTactic (← `(tactic| cases $(mkIdent name):ident))
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      step s iteration subtypes
    return
  if let some f ← generatedIndexedList then
    traceStep m!"cases {← withMainContext do pure (← f.getDecl).userName} (generated index)"
    let subgoals ← (← getMainGoal).cases f
    for g in subgoals.map (·.mvarId) do
      setGoals [g]
      step s iteration subtypes
    return
  if ← tryTac (evalTactic (← `(tactic| contradiction))) then return
  let goal ← getMainGoal
  try stepCore s goal iteration subtypes
  catch e =>
    let msg := e.toMessageData
    if ((← msg.toString).splitOn "during ").length > 1 then throw e
    let ty ← goal.withContext do instantiateMVars (← goal.getType)
    let head := if ty.isAppOfArity ``Refines 5 then chainHead (ty.getArg! 3) else ty
    let gen := if ty.isAppOfArity ``Refines 5 then chainHead (ty.getArg! 4) else ty
    goal.withContext do throwError "{msg}\nduring {← phaseNow.get}, at the interpreter step\
      {indentExpr head}\nagainst the generated{indentExpr gen}"

/-- The step proper, on `goal`. -/
partial def stepCore (s : SimpSet) (goal : MVarId)
    (iteration : Option Expr := none) (subtypes : Bool := false) : TacticM Unit := do
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
    if subtypes then elementResults n
    -- a batch's positional column relation keeps its encoders for column collection;
    -- normalizing it would compute a list column's canonical form in place of its encoder
    let columnRelation ← columnRelationHyp n
    let _ ← tryTac (evalTactic (← `(tactic| dsimp only at $(mkIdent n):ident)))
    unless columnRelation do
      let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel, Outs] at $(mkIdent n):ident)))
      let _ ← tryTac (evalTactic (← `(tactic| dsimp only at $(mkIdent n):ident)))
      let _ ← normalizeAt s n
    if subtypes && !(← getGoals).isEmpty then
      let conjunction ← withMainContext do
        let some declaration := (← getLCtx).findFromUserName? n | return false
        return (← whnf (← instantiateMVars declaration.type)).isAppOfArity ``And 2
      if conjunction then
        let left ← freshName "rf_g_left"
        let isLength ← withMainContext do
          let some declaration := (← getLCtx).findFromUserName? n | return false
          let type ← whnf (← instantiateMVars declaration.type)
          let some (_, lhs, _) := (type.getArg! 1).eq? | return false
          return lhs.isAppOfArity ``List.length 2
        let right ← freshName (if isLength then "rf_c_traversalLength" else "rf_g_right")
        evalTactic (← `(tactic|
          obtain ⟨$(mkIdent left):ident, $(mkIdent right):ident⟩ := $(mkIdent n):ident))
    expose
    return ← step s iteration subtypes
  let some (_, m, n) ← refinesGoal
    | throwError "refine_al: not a refinement goal:{Lean.MessageData.ofGoal goal}"
  -- table entries the interpreter looks up
  if ← tableFacts (← libOf) then
    let _ ← normalize s
    return ← step s iteration subtypes
  let head := chainHead m
  if subtypes then
    if ← emptyTraversalResult head then return ← step s iteration subtypes
    if ← columnTraversalResult head then return ← step s iteration subtypes
    if head.isAppOfArity ``Ctx.transpose 1 then
      if ← normalize s then return ← step s iteration subtypes
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
    return ← step s iteration subtypes
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
      step s iteration subtypes
    return
  -- ordered list traversals retain the actual reference contexts
  if ← lookupTraversal s then return ← step s iteration subtypes
  let relation ← match iteration with
    -- the source-derived relation observes the contexts a pattern traversal produces; with
    -- the subtype preset, other traversals keep their own element relations
    | some relation => withMainContext do
      if !subtypes then return some relation
      if head.isAppOfArity ``List.mapM 6 &&
          (← isDefEq (head.getArg! 3) (mkConst ``P4SpecTec.Interp_al.Ctx.t)) then
        return some relation
      if let some relation ← columnTraversalRelation m n then return some relation
      let generated := chainHead n
      if head.isAppOfArity ``List.mapM 6 && generated.isAppOfArity ``List.mapM 6 then
        if ← isDefEq (head.getArg! 3) (mkConst ``P4SpecTec.Lang.Il.value) then
          let element ← Term.exprToSyntax (generated.getArg! 3)
          return some (← Term.elabTerm (← `(@P4SpecTec.Refine.Rel $element _)) none)
      return none
    | none => withMainContext do
      if subtypes then
        if let some relation ← columnTraversalRelation m n then return some relation
      let generated := chainHead n
      if subtypes && head.isAppOfArity ``List.mapM 6 &&
          generated.isAppOfArity ``List.mapM 6 then
        if (← isDefEq (head.getArg! 3) (mkApp (mkConst ``List [Level.zero])
            (mkConst ``P4SpecTec.Lang.Il.value))) &&
            (← isDefEq (generated.getArg! 3) (mkConst ``Unit)) then
          return some (← Term.elabTerm
            (← `(fun (row : List P4SpecTec.Lang.Il.value) (_ : Unit) => row = [])) none)
        -- an iterated expression: each reference element value represents its generated one
        if ← isDefEq (head.getArg! 3) (mkConst ``P4SpecTec.Lang.Il.value) then
          let element ← Term.exprToSyntax (generated.getArg! 3)
          return some (← Term.elabTerm
            (← `(@P4SpecTec.Refine.Rel $element _)) none)
      return none
  if let some relation := relation then
    if ← mapMGoals s relation m n then
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        step s iteration subtypes
      return
  if subtypes then
    if ← pureMapTraversal s m n then
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        step s iteration subtypes
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
      -- the reference step at zero fuel has no result by its defining equation; closing
      -- it directly avoids normalizing the whole goal to discover the divergence
      if ← tryTac (evalTactic (← `(tactic|
          first | exact refines_bind_of_none rfl | exact refines_of_none rfl))) then
        continue
      -- `step` normalizes first
      step s iteration subtypes
    return
  -- a pure result
  if head.isAppOfArity ``Pure.pure 4 && (chainTail m).isNone then
    unless n.isAppOfArity ``Pure.pure 4 do
      if ← closeBoolConflict then return
      if ← closeConstructorClash then return
      if ← closeValueEqConflict s then return
      if ← splitGeneratedList s n (step s iteration subtypes) then return
      if ← splitGeneratedDiscriminant s n (step s iteration subtypes) then return
      if ← splitGeneratedCondition s n (step s iteration subtypes) then return
      if ← splitFactList s (step s iteration subtypes) then return
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
    if ← tryTac (evalTactic (← `(tactic| exact refines_throw))) then return
    -- An unresolved generated option can still determine a source pattern mismatch.
    let option ← goal.withContext do
      let ((), vars) ← ((← instantiateMVars n).collectFVars).run {}
      let mut found : Option FVarId := none
      for f in vars.fvarIds do
        if found.isNone && (← whnfR (← f.getType)).isAppOfArity ``Option 1 then
          found := some f
      pure found
    if let some f := option then
      let name ← goal.withContext do pure (← f.getDecl).userName
      evalTactic (← `(tactic| cases $(mkIdent name):ident))
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        step s iteration subtypes
      return
    if ← closeBoolConflict then return
    if ← closeConstructorClash then return
    if ← closeValueEqConflict s then return
    if ← splitGeneratedList s n (step s iteration subtypes) then return
    if ← splitGeneratedDiscriminant s n (step s iteration subtypes) then return
    if ← splitGeneratedCondition s n (step s iteration subtypes) then return
    if ← splitFactList s (step s iteration subtypes) then return
    throwError "refine_al: the interpreter fails but the generated code does not fail alike:\
      {Lean.MessageData.ofGoal goal}"
  -- an invocation
  if invocations.any (head.isAppOf ·) then
    -- the generated side may still project a value the reference side already used
    if !(chainHead n).isAppOfArity ``ExceptT.mk 4 then
      if ← splitGeneratedDiscriminant s n (step s iteration subtypes) then return
      if ← splitGeneratedList s n (step s iteration subtypes) then return
      if ← splitGeneratedCondition s n (step s iteration subtypes) then return
    noteAction "callee"
    let tail := (chainTail m).isNone
    calleeStep s m n
    -- an impossible branch may have closed the goal instead of pairing the calls
    if (← getGoals).isEmpty then return
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
    return ← step s iteration subtypes
  -- a generated test and the reference test of the same step, decided together
  if ← alignTest s m n then
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let hc ← withMainContext do
        let decls := (← getLCtx).decls.toList.filterMap id
        pure (decls.filter (·.userName.toString.startsWith "rf_c")).getLast?
      if let some hc := hc then
        let _ ← tryTac (evalTactic (← `(tactic| simp only [$(mkIdent hc.userName):ident])))
      if (← getGoals).isEmpty then continue
      step s iteration subtypes
    return
  -- the generated side: a match or `if` on a variable, or on a projection
  -- of a variable of a generated structure (destructured first, so that
  -- the projection computes)
  if let some d ← generatedDiscriminant n then
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
      -- `step` normalizes the goal first, now with the exposed facts
      noteAction "cases generated: step"
      step s iteration subtypes
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
      -- `step` normalizes the goal first
      step s iteration subtypes
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
      if ← closeArithmetic then continue
      -- `step` normalizes the goal first
      step s iteration subtypes
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
        step s iteration subtypes
      return
  goal.withContext do
    throwError "refine_al: stuck at the interpreter step{indentExpr head}\nagainst the generated\
      {indentExpr (chainHead n)}\nin{Lean.MessageData.ofGoal goal}"

end

/-- The tactic's body. -/
def refineAl (s : SimpSet) (iteration : Option Expr := none)
    (subtypes : Bool := false) : TacticM Unit := do
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
  try step s iteration subtypes
  finally traceStep m!"phase times (ms): {← phaseTimes.get}"
  unless (← getGoals).isEmpty do throwError "refine_al: goals left open"

/-- Close `Holds g d` for a quoted declaration `d` of the specification hypothesis. -/
elab "holds_from_spec" : tactic => do
  unless ← declarationFromSpec do
    throwError "holds_from_spec: the goal is not a quoted declaration of the specification"

/-- The tactic: see the module docstring. -/
elab "refine_al" : tactic => do
  let s ← simpSet
  -- no error recovery: a failing step must fail the proof, not admit a goal
  try withoutRecover do refineAl (← prepareSimpSet s)
  catch e =>
    throwError "{e.toMessageData}\n(last action: {← phaseNow.get})"

/-- Forward iteration with a checked, syntax-derived intermediate value relation. -/
elab "refine_al" "(" "iteration" ":=" relation:term ")" : tactic => do
  introNamed
  let q ← Term.elabTerm relation none
  let s ← simpSet
  try withoutRecover do refineAl (← prepareSimpSet s) (some q)
  catch e => throwError "{e.toMessageData}\n(last action: {← phaseNow.get})"

/-- Forward execution using exact outer subtype checks and generated subtype bridges. -/
elab "refine_al" "(" "subtypes" ")" : tactic => do
  let rules ← subtypeSimpSet
  let s := { rules with
    lemmas := rules.lemmas.filter (fun name => !(``Ctx.transpose).isPrefixOf name) ++
      #[``orElseAssoc, ``unmatchOrElse, ``pureOrElse, ``errorOrElse, ``bindOrElse, ``haveOrElse,
        ``transposeEmptyRows, ``List.mapM_map]
    procs := rules.procs.push ``iterPremListNoOutputs }
  try withoutRecover do refineAl (← prepareSimpSet s) none true
  catch e => throwError "{e.toMessageData}\n(last action: {← phaseNow.get})"

/-- Forward execution with the subtype preset and a checked, syntax-derived relation for
pattern traversals; other traversals keep the subtype preset's element relations. -/
elab "refine_al" "(" "subtypes" ")" "(" "iteration" ":=" relation:term ")" : tactic => do
  introNamed
  let q ← Term.elabTerm relation none
  let rules ← subtypeSimpSet
  let s := { rules with
    lemmas := rules.lemmas.filter (fun name => !(``Ctx.transpose).isPrefixOf name) ++
      #[``orElseAssoc, ``unmatchOrElse, ``pureOrElse, ``errorOrElse, ``bindOrElse, ``haveOrElse,
        ``transposeEmptyRows, ``List.mapM_map]
    procs := rules.procs.push ``iterPremListNoOutputs }
  try withoutRecover do refineAl (← prepareSimpSet s) (some q) true
  catch e => throwError "{e.toMessageData}\n(last action: {← phaseNow.get})"

/-- Forward list premises with separately encoded output columns at each traversal. -/
elab "refine_al" "(" "columns" ")" : tactic => do
  let rules ← subtypeSimpSet
  let s := { rules with
    lemmas := rules.lemmas.filter (fun name => !(``Ctx.transpose).isPrefixOf name) ++
      #[``orElseAssoc, ``unmatchOrElse, ``pureOrElse, ``errorOrElse, ``bindOrElse, ``haveOrElse,
        ``transposeEmptyRows, ``List.mapM_map]
    procs := rules.procs.push ``iterPremListColumns }
  try withoutRecover do refineAl (← prepareSimpSet s) none true
  catch e => throwError "{e.toMessageData}\n(last action: {← phaseNow.get})"

end P4SpecTec.Tactic
