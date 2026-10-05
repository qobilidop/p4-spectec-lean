import P4SpecTec.Tactic.StateRunSound
import P4SpecTec.Tactic.OutcomeInduction

/-!
State run-soundness of a recursive group, by one induction over its least fixed point (not
a mirror). A `partial_fixpoint` group is `Lean.Order.fix F hmono`, read from the
definitions' values; `Lean.Order.fix_induct` runs with the motive that an approximant is
below the fixed point and that each of its relations is sound. Each step is then proved by
the symbolic execution of `Tactic/StateRunSound.lean`.

Lean's derived `partial_correctness` is not used: its derivation fails for a definition
with a long parameter list, where instance resolution does not find the pointwise order of
the function type. Here every order instance is read off the fixed point's own, and the
terms whose types are as large as the group (admissibility, the split of the step, the
componentwise order facts) are built explicitly: their types differ from what unification
would compare only by unfolding the group's definitions, which the kernel does directly.
-/

namespace P4SpecTec.Tactic.StateSound

open Lean Elab Tactic Meta

/-- Reduce projections of explicit tuples, and the applications they expose. -/
def reduceComponents (e : Expr) : MetaM Expr :=
  Core.transform e (post := fun e => do
    let reduced := match e with
      | .proj owner index tuple =>
        let tuple := tuple.consumeMData
        if owner == ``PProd && tuple.isAppOfArity ``PProd.mk 4 then tuple.getArg! (2 + index)
        else e
      | _ =>
        let f := e.getAppFn
        let n := e.getAppNumArgs
        if (f.isConstOf ``PProd.fst || f.isConstOf ``PProd.snd) && n ≥ 3 &&
            (e.getArg! 2).consumeMData.isAppOfArity ``PProd.mk 4 then
          mkAppN ((e.getArg! 2).consumeMData.getArg! (if f.isConstOf ``PProd.fst then 2 else 3))
            (e.getAppArgs.extract 3 n)
        else e
    pure (.done (if reduced.isHeadBetaTarget then reduced.headBeta else reduced)))

/-- Reduce the head of an application of a tuple component: the unfolding of a group's
functional at explicit components, selected and applied, without traversing the rest. -/
partial def headReduce (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  let f := e.getAppFn
  let args := e.getAppArgs
  let select (index : Nat) (tuple : Expr) (rest : Array Expr) : MetaM Expr := do
    let tuple := (← headReduce tuple).consumeMData
    if tuple.isAppOfArity ``PProd.mk 4 then headReduce (mkAppN (tuple.getArg! (2 + index)) rest)
    else pure e
  match f with
  | .lam .. => if args.isEmpty then pure e else headReduce (f.beta args)
  | .proj owner index tuple => if owner == ``PProd then select index tuple args else pure e
  | .const name _ =>
    if name == ``PProd.fst && args.size ≥ 3 then select 0 args[2]! (args.extract 3 args.size)
    else if name == ``PProd.snd && args.size ≥ 3 then
      select 1 args[2]! (args.extract 3 args.size)
    else pure e
  | _ => pure e

/-- A group's tuple type, level by level: at depth `d` the tuple `α ×' β` with the order
instances of both sides, where `β` is the tuple at depth `d + 1` or the last component. -/
structure TupleLevel where
  /-- The first component's type. -/
  first : Expr
  /-- The type of the remaining components. -/
  rest : Expr
  /-- The order of the first component. -/
  firstOrder : Expr
  /-- The order of the remaining components. -/
  restOrder : Expr
  deriving Inhabited

/-- The levels of a group of `count` definitions, from the order instance of its tuple.
Instances are read off, never synthesized: resolution does not scale to large groups. -/
def tupleLevels (type order : Expr) (count : Nat) : MetaM (Array TupleLevel) := do
  let mut out := #[]
  let mut type := type
  let mut order := order
  for _ in [0:count - 1] do
    let found := order.consumeMData
    let tuple := type.consumeMData
    unless found.isAppOfArity ``Lean.Order.instCCPOPProd 4 && tuple.isAppOfArity ``PProd 2 do
      throwError "state_run_sound: unexpected order of a group's tuple: {order}"
    out := out.push { first := tuple.getArg! 0, rest := tuple.getArg! 1
                      firstOrder := found.getArg! 2, restOrder := found.getArg! 3 }
    type := tuple.getArg! 1
    order := found.getArg! 3
  pure out

/-- `admissible (fun x => Q (component x))` for the component at `position` of a group
value, from `hQ : admissible Q` at that component's type. -/
def componentAdmissible (levels : Array TupleLevel) (position : Nat) (Q hQ : Expr) :
    MetaM Expr := do
  let count := levels.size + 1
  let step (first : Bool) (depth : Nat) (Q hQ : Expr) : MetaM (Expr × Expr) := do
    let level := levels[depth]!
    let proof ← mkAppOptM
      (if first then ``Lean.Order.admissible_pprod_fst else ``Lean.Order.admissible_pprod_snd)
      #[level.first, level.rest, level.firstOrder, level.restOrder, Q, hQ]
    let tuple ← mkAppM ``PProd #[level.first, level.rest]
    let next ← withLocalDeclD `p tuple fun p => do
      mkLambdaFVars #[p] ((mkApp Q (← mkAppM (if first then ``PProd.fst else ``PProd.snd)
        #[p])).headBeta)
    pure (next, proof)
  let mut current := (Q, hQ)
  let mut depth := position
  if position + 1 < count then
    current ← step true position current.1 current.2
  while depth > 0 do
    depth := depth - 1
    current ← step false depth current.1 current.2
  pure current.2

/-- `admissible (fun x => Q (e x))` from `hQ : admissible Q`, where `e` applies a component
of the group value `x` to arguments without `x`. The pointwise order of each application is
read off the component's own order instance: resolution fails on long function types. -/
def liftAdmissible (x : Expr) (components : Array Expr) (levels : Array TupleLevel)
    (order e Q hQ : Expr) : MetaM Expr := do
  -- peel the arguments down to the component
  let mut reversed := #[]
  let mut head := e.consumeMData
  let mut found : Option Nat := none
  while found.isNone do
    if let some position := components.idxOf? head then
      found := some position
    else match head with
      | .app f a =>
        reversed := reversed.push a
        head := f.consumeMData
      | _ => throwError "state_run_sound: unexpected group component: {e}"
  let some position := found | throwError "state_run_sound: unexpected group component: {e}"
  let args := reversed.reverse
  let count := levels.size + 1
  -- the order of the function each argument is applied to
  let mut current := if count == 1 then order
    else if position + 1 < count then levels[position]!.firstOrder
    else levels[count - 2]!.restOrder
  let mut families := #[]
  for a in args do
    let pointwise := current.consumeMData
    unless pointwise.isAppOfArity ``Lean.Order.instCCPOPi 3 do
      throwError "state_run_sound: unexpected order of a group component: {current}"
    families := families.push (pointwise.getArg! 0, pointwise.getArg! 1, pointwise.getArg! 2)
    current := (mkApp (pointwise.getArg! 2) a).headBeta
  -- from the last argument inward
  let mut predicate := Q
  let mut proof := hQ
  for offset in [0:args.size] do
    let index := args.size - 1 - offset
    let a := args[index]!
    if a.containsFVar x.fvarId! then
      throwError "state_run_sound: a recursive call's argument mentions the group: {e}"
    let (domain, codomain, family) := families[index]!
    proof ← mkAppOptM ``Lean.Order.admissible_apply
      #[domain, codomain, family, Expr.lam `_ domain predicate .default, a, proof]
    let function := mkAppN components[position]! (args.extract 0 index)
    let applied := predicate
    predicate ← withLocalDeclD `f (← inferType function) fun g => do
      mkLambdaFVars #[g] ((mkApp applied (mkApp g a)).headBeta)
  componentAdmissible levels position predicate proof

/-- `admissible (fun x => body)` for a relation's soundness statement over the group value
`x`: binders without `x`, then one run equation of a component of `x` with a defined
outcome, then a conclusion without `x`. `type` and `order` are the group's. -/
partial def admissibleOf (type order x : Expr) (components : Array Expr)
    (levels : Array TupleLevel) (body : Expr) : MetaM Expr := do
  match body.consumeMData with
  | .forallE name domain rest info =>
    if domain.containsFVar x.fvarId! then
      if rest.hasLooseBVars || rest.containsFVar x.fvarId! then
        throwError "state_run_sound: a soundness conclusion mentions the group or its run"
      let some (_, lhs, rhs) := domain.consumeMData.eq?
        | throwError "state_run_sound: a soundness hypothesis is not a run equation"
      let rhs := rhs.consumeMData
      unless rhs.isAppOfArity ``Option.some 2 && !rhs.containsFVar x.fvarId! do
        throwError "state_run_sound: a soundness hypothesis has no defined outcome"
      let outcome ← withLocalDeclD `o (← inferType lhs) fun o => do
        mkLambdaFVars #[o] (← mkArrow (← mkEq o rhs) rest)
      let proof ← mkAppM ``Lean.Order.Option.admissible_eq_some #[rest, rhs.getArg! 1]
      liftAdmissible x components levels order lhs outcome proof
    else
      withLocalDecl name info domain fun y => do
        let inner := rest.instantiate1 y
        let proof ← admissibleOf type order x components levels inner
        mkAppOptM ``Lean.Order.admissible_pi
          #[type, order, none, ← mkLambdaFVars #[x, y] inner, ← mkLambdaFVars #[y] proof]
  | _ => throwError "state_run_sound: a soundness statement has no run hypothesis"

/-- The position of a definition in its group's tuple, from the projections its value
applies to the group's constant: the number of second projections. -/
partial def tuplePosition : Expr → Nat
  | .proj _ index tuple => tuplePosition tuple + index
  | e =>
    if e.isAppOfArity ``PProd.fst 3 then tuplePosition (e.getArg! 2)
    else if e.isAppOfArity ``PProd.snd 3 then tuplePosition (e.getArg! 2) + 1
    else 0

/-- The value a chain of tuple projections selects from. -/
partial def tupleBase : Expr → Expr
  | .proj _ _ s => tupleBase s
  | e => if e.isAppOfArity ``PProd.fst 3 || e.isAppOfArity ``PProd.snd 3
    then tupleBase (e.getArg! 2) else e

/-- Prove the joint soundness statement of a recursive group. `members` are all its
definitions, functions included; the goal is a conjunction of the state run-soundness
statements of its relations. The group's fixed point may be abstracted over leading
arguments found in the theorem's context (the extern instance) and nothing else. -/
def proveStateGroup (members consumers : Array Name) : TacticM Unit := withoutRecover do
  let goal ← getMainGoal
  let count := members.size
  if count == 0 then throwError "state_run_sound: empty group"
  -- the group's fixed point: the first member's value, or the constant it projects
  let strip (e : Expr) : Expr × Nat := Id.run do
    let mut e := e
    let mut k := 0
    while e.isLambda do
      e := e.bindingBody!
      k := k + 1
    pure (e, k)
  let (fixName, fixedCount) ← do
    let (body, k) := strip (← getConstInfo members[0]!).value!
    let tuple := tupleBase body
    if tuple.isAppOf ``Lean.Order.fix then pure (members[0]!, k)
    else match tuple.getAppFn with
      | .const name _ => pure (name, k)
      | _ => throwError "state_run_sound: {members[0]!} is not a member of a fixed point"
  -- the definitions in the order of the group's tuple, which is Lean's, not the source's
  let mut ordered : Array Name := Array.replicate count Name.anonymous
  for name in members do
    let value := (← getConstInfo name).value!
    let position := if count == 1 then 0 else tuplePosition (strip value).1
    unless position < count && ordered[position]! == Name.anonymous do
      throwError "state_run_sound: {name} has no position of its own in the group"
    ordered := ordered.set! position name
  let members := ordered
  let (motive, admissible, stepType, fixValue, parts, relations, memberApps, levels) ←
      goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let parts := (conjuncts target).toArray
    let relations ← parts.mapM fun part => do
      let some name := conjunctFunction part
        | throwError "state_run_sound: a conjunct names no definition"
      let some index := members.idxOf? name
        | throwError "state_run_sound: {name} is not a listed member"
      pure index
    -- the leading arguments the fixed point is abstracted over (the extern instance)
    let fixedArgs ← forallTelescope parts[0]! fun xs _ => do
      for x in xs do
        if let some (_, lhs, _) := (← instantiateMVars (← inferType x)).consumeMData.eq? then
          if lhs.getAppFn.isConst then return lhs.getAppArgs.extract 0 fixedCount
      throwError "state_run_sound: a conjunct has no run hypothesis"
    -- Only arguments of the theorem's own context are supported: generated definitions
    -- rebind every parameter, so Lean abstracts nothing but the extern instance.
    let context ← getLCtx
    unless fixedArgs.size == fixedCount &&
        fixedArgs.all (fun a => a.isFVar && context.contains a.fvarId!) do
      throwError "state_run_sound: {fixName} is abstracted over a parameter of the \
        statement; only arguments in the theorem's context, such as the extern instance, \
        are supported"
    let fixValue := ((← getConstInfo fixName).value!.beta fixedArgs).consumeMData
    unless fixValue.isAppOfArity ``Lean.Order.fix 4 do
      throwError "state_run_sound: {fixName} is not a least fixed point of its definitions \
        alone; a parameter passed on unchanged is abstracted from it, which is not supported"
    let type := fixValue.getArg! 0
    let order := fixValue.getArg! 1
    let functional := fixValue.getArg! 2
    let levels ← tupleLevels type order count
    let memberApps := members.map fun name => mkAppN (mkConst name) fixedArgs
    let below (x y : Expr) : MetaM Expr := do
      mkAppOptM ``Lean.Order.PartialOrder.rel
        #[type, ← mkAppOptM ``Lean.Order.CCPO.toPartialOrder #[type, order], x, y]
    withLocalDeclD `x type fun x => do
      -- the components of a group value, as the order lemmas state them
      let components ← withLocalDeclD `h (← below x fixValue) fun h => do
        let mut out := #[]
        let mut current := h
        for index in [0:count] do
          let proof ← if count == 1 || index == count - 1 then pure current
            else
              let level := levels[index]!
              mkAppOptM ``P4SpecTec.Refine.pprodLeFst
                #[level.first, level.rest, level.firstOrder, level.restOrder, none, none, current]
          out := out.push ((← instantiateMVars (← inferType proof)).getArg! 2)
          if index + 1 < count then
            let level := levels[index]!
            current ← mkAppOptM ``P4SpecTec.Refine.pprodLeSnd
              #[level.first, level.rest, level.firstOrder, level.restOrder, none, none, current]
        pure out
      let statement (index : Nat) (replacement : Expr) : Expr :=
        parts[index]!.replace fun e =>
          if e == memberApps[relations[index]!]! then some replacement else none
      let statements := (List.range parts.size).map fun i =>
        statement i components[relations[i]!]!
      let conjunction (ps : List Expr) : Expr :=
        ps.dropLast.foldr (fun a acc => mkApp2 (mkConst ``And) a acc) ps.getLast!
      let sound := conjunction statements
      let motive ← mkLambdaFVars #[x]
        (mkApp2 (mkConst ``And) (← below x fixValue) sound)
      -- admissibility, conjunct by conjunct
      let mut proofs : List (Expr × Expr) := []
      for body in statements do
        proofs := proofs ++ [(← mkLambdaFVars #[x] body,
          ← admissibleOf type order x components levels body)]
      let rec join : List (Expr × Expr) → MetaM (Expr × Expr)
        | [] => throwError "state_run_sound: no relation in the group statement"
        | [p] => pure p
        | (predicate, proof) :: rest => do
          let (restPredicate, restProof) ← join rest
          let both ← withLocalDeclD `x type fun y => do
            mkLambdaFVars #[y] (mkApp2 (mkConst ``And) (predicate.beta #[y])
              (restPredicate.beta #[y]))
          pure (both, ← mkAppOptM ``Lean.Order.admissible_and
            #[type, order, predicate, restPredicate, proof, restProof])
      let (soundPredicate, soundProof) ← join proofs
      let belowPredicate ← mkLambdaFVars #[x] (← below x fixValue)
      let belowProof ← mkAppOptM ``P4SpecTec.Refine.admissibleLe #[type, order, fixValue]
      let admissible ← mkAppOptM ``Lean.Order.admissible_and
        #[type, order, belowPredicate, soundPredicate, belowProof, soundProof]
      let stepType ← mkForallFVars #[x] (← mkArrow (motive.beta #[x])
        (motive.beta #[mkApp functional x]))
      pure (motive, admissible, stepType, fixValue, parts, relations, memberApps, levels)
  let type := fixValue.getArg! 0
  let order := fixValue.getArg! 1
  let step ← mkFreshExprSyntheticOpaqueMVar stepType
  goal.withContext do
    let induction ← mkAppOptM ``Lean.Order.fix_induct
      #[type, order, fixValue.getArg! 2, fixValue.getArg! 3, motive, admissible, step]
    let result ← mkAppM ``And.right #[induction]
    -- the statement over the fixed point is the statement over the definitions, unfolded
    unless ← withTransparency .all (isDefEq (← inferType result) (← goal.getType)) do
      throwError "state_run_sound: the induction does not conclude the group statement"
    goal.assign result
  -- the step: components `g`, each below its definition, and sound where a relation
  setGoals [step.mvarId!]
  let x ← freshName "ss_g"
  let hypothesis ← freshName "ss_m"
  evalTactic (← `(tactic| intro $(mkIdent x):ident $(mkIdent hypothesis):ident))
  let mut approximantNames := #[x]
  if count > 1 then
    approximantNames := #[]
    let mut remaining := x
    for index in [0:count - 1] do
      let first := Name.mkSimple s!"{x}_{index}"
      let second := Name.mkSimple s!"{x}_{index}'"
      evalTactic (← `(tactic| cases $(mkIdent remaining):ident with
        | mk $(mkIdent first):ident $(mkIdent second):ident => ?_))
      approximantNames := approximantNames.push first
      remaining := second
    approximantNames := approximantNames.push remaining
  let belowName ← freshName "ss_below"
  let mut ihNames := (List.range parts.size).toArray.map fun i => Name.mkSimple s!"ss_ih{i}"
  let mut soundName := Name.mkSimple s!"{hypothesis}'"
  evalTactic (← `(tactic| cases $(mkIdent hypothesis):ident with
    | intro $(mkIdent belowName):ident $(mkIdent soundName):ident => ?_))
  for i in [0:parts.size] do
    if i + 1 == parts.size then
      ihNames := ihNames.set! i soundName
    else
      let rest := Name.mkSimple s!"{soundName}'"
      evalTactic (← `(tactic| cases $(mkIdent soundName):ident with
        | intro $(mkIdent ihNames[i]!):ident $(mkIdent rest):ident => ?_))
      soundName := rest
  -- Every approximant is below its definition, componentwise, and the induction
  -- hypotheses speak of the components themselves. These hypotheses and the split of the
  -- goal are built as terms: their types differ from what unification would compare only by
  -- unfolding the group's definitions, which the kernel does directly.
  do
    let goal ← getMainGoal
    let facts ← goal.withContext do
      let mut current := mkFVar (← fvarOf belowName)
      let mut out := #[]
      for index in [0:count] do
        let proof ← if count == 1 || index == count - 1 then pure current
          else
            let level := levels[index]!
            mkAppOptM ``P4SpecTec.Refine.pprodLeFst
              #[level.first, level.rest, level.firstOrder, level.restOrder, none, none, current]
        let type := (← instantiateMVars (← inferType proof)).consumeMData
        unless type.isAppOfArity ``Lean.Order.PartialOrder.rel 4 do
          throwError "state_run_sound: unexpected order statement {type}"
        let approximant := mkFVar (← fvarOf approximantNames[index]!)
        let stated := mkApp4 type.getAppFn (type.getArg! 0) (type.getArg! 1) approximant
          memberApps[index]!
        out := out.push (Name.mkSimple s!"ss_le{index}", stated, proof)
        if index + 1 < count then
          let level := levels[index]!
          current ← mkAppOptM ``P4SpecTec.Refine.pprodLeSnd
            #[level.first, level.rest, level.firstOrder, level.restOrder, none, none, current]
      pure out
    let mut current := goal
    for (name, type, proof) in facts do
      let (_, next) ← (← current.assert name type proof).intro1P
      current := next
    setGoals [current]
  -- each induction hypothesis over its component, kept from simplification
  for i in [0:parts.size] do
    let goal ← getMainGoal
    let ih ← fvarOf ihNames[i]!
    let (type, proof) ← goal.withContext do
      let reduced ← reduceComponents (← instantiateMVars (← ih.getType))
      pure (← mkAppM ``P4SpecTec.Refine.Kept #[reduced],
        ← mkAppOptM ``P4SpecTec.Refine.Kept.mk #[reduced, mkFVar ih])
    let (_, goal) ← (← goal.assert (Name.mkSimple s!"ss_ih{i}") type proof).intro1P
    setGoals [← goal.clear ih]
  -- the goal: one unfolding is below the fixed point, and sound for each relation
  do
    let goal ← getMainGoal
    let cases ← goal.withContext do
      let target := (← instantiateMVars (← goal.getType)).consumeMData
      unless target.isAppOfArity ``And 2 do
        throwError "state_run_sound: the induction step is not a conjunction"
      let below ← mkAppOptM ``P4SpecTec.Refine.fixStepLe
        #[type, order, fixValue.getArg! 2, fixValue.getArg! 3, none, mkFVar (← fvarOf belowName)]
      let rec split (type : Expr) (n : Nat) : MetaM (Expr × List MVarId) := do
        let type := type.consumeMData
        if n ≤ 1 then
          let hole ← mkFreshExprSyntheticOpaqueMVar type
          pure (hole, [hole.mvarId!])
        else
          unless type.isAppOfArity ``And 2 do
            throwError "state_run_sound: the induction step has too few conjuncts"
          let first ← mkFreshExprSyntheticOpaqueMVar (type.getArg! 0)
          let (rest, holes) ← split (type.getArg! 1) (n - 1)
          pure (mkApp4 (mkConst ``And.intro) (type.getArg! 0) (type.getArg! 1) first rest,
            first.mvarId! :: holes)
      let (sound, holes) ← split (target.getArg! 1) parts.size
      goal.assign (mkApp4 (mkConst ``And.intro) (target.getArg! 0) (target.getArg! 1) below sound)
      pure holes
    setGoals cases
  let cases ← getGoals
  for case in cases, i in [0:cases.length] do
    setGoals [case]
    let member := members[relations[i]!]!
    -- the unfolded functional is as large as the group: nothing later may traverse it
    evalTactic (← `(tactic| clear $(mkIdent belowName):ident))
    let introduced ← introAll
    let some hr := introduced.getLast? | throwError "state_run_sound: empty induction case"
    -- the attempts take the member's arguments but the state: the fixed ones, then the
    -- statement's first binders
    do
      let fixedArgs := memberApps[relations[i]!]!.getAppArgs
      let arity ← forallTelescope (← getConstInfo member).type fun xs _ => pure xs.size
      let own := arity - fixedArgs.size - 1
      let params ← (introduced.take own).toArray.mapM fun name => do pure (mkFVar (← fvarOf name))
      nameAttempts (fixedArgs ++ params)
    timed s!"{member} unfolding" do
      let goal ← getMainGoal
      let hid ← fvarOf hr
      let reduced ← goal.withContext do
        let type ← instantiateMVars (← hid.getType)
        let some (_, lhs, rhs) := type.consumeMData.eq?
          | throwError "state_run_sound: an induction case has no run hypothesis"
        mkEq (← reduceComponents (← headReduce lhs)) rhs
      setGoals [← goal.replaceLocalDeclDefEq hid reduced]
    timed s!"{member} execution" (execute consumers [hr])
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      timed s!"{member} rule" (closeStateGoal consumers)
      unless (← openGoals (← getGoals)).isEmpty do
        throwError "state_run_sound: a rule of {member} is left open"
  setGoals []

/-- Prove the joint statement of a recursive group by induction over its fixed point.
The first list names every definition of the group; the second the callback consumers the
group's own monotonicity proof may expose. -/
elab "state_run_sound_group " "[" members:ident,* "]" "[" consumers:ident,* "]" : tactic => do
  let members ← members.getElems.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
  let consumers ← consumers.getElems.mapM fun id => realizeGlobalConstNoOverloadWithInfo id
  proveStateGroup members consumers

end P4SpecTec.Tactic.StateSound
