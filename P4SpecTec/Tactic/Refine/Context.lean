import Lean.Elab.Tactic.RCases
import Lean.Elab.Tactic.Generalize
import Lean.Meta.Match.MatcherApp.Basic
import P4SpecTec.Tactic.Refine.ForwardRules
import P4SpecTec.Tactic.RunSound

/-!
Refinement-goal context: accessible binders, monadic and fuel shapes, generated
value counterparts, quoted global-table facts and representation exposure.
The shape queries identify interpreter calls using the forward rule inventory.
-/

namespace P4SpecTec.Tactic

open Lean Elab Tactic Meta
open P4SpecTec.Refine
open P4SpecTec.Interp_al

/-- Introduce every binder of the goal under an accessible name (the
binder's own when free), so that the facts can be named. -/
partial def introNamed : TacticM Unit := do
  let goal ← getMainGoal
  let ty ← goal.withContext do whnfR (← instantiateMVars (← goal.getType))
  match ty.consumeMData with
  | .forallE bn _ _ _ =>
    let n := if bn.isAnonymous || bn.hasMacroScopes then `rf_x else bn
    let n ← if (← goal.withContext do pure ((← getLCtx).findFromUserName? n).isSome)
      then freshName n.toString else pure n
    evalTactic (← `(tactic| intro $(mkIdent n):ident))
    introNamed
  | _ => pure ()

/-! ## Shapes -/

/-- The head of a monadic chain: `m₁` of `m₁ >>= k`, else the term. -/
def chainHead (m : Expr) : Expr :=
  let m := m.consumeMData
  if m.isAppOfArity ``Bind.bind 6 then (m.getArg! 4).consumeMData else m

/-- The continuation of a monadic chain, if it is a bind. -/
def chainTail (m : Expr) : Option Expr :=
  let m := m.consumeMData
  if m.isAppOfArity ``Bind.bind 6 then some (m.getArg! 5) else none

/-- The `Refines P m n` of the goal. -/
def refinesGoal : TacticM (Option (Expr × Expr × Expr)) := do
  let goal ← getMainGoal
  goal.withContext do
    let ty := (← instantiateMVars (← goal.getType)).consumeMData
    if ty.isAppOfArity ``Refines 5 then
      pure (some ((ty.getArg! 2).consumeMData, (ty.getArg! 3).consumeMData,
        (ty.getArg! 4).consumeMData))
    else pure none

/-- Find the first explicit `Nat` parameter of an interpreter call. Its
signature identifies fuel without assuming that it precedes implicit carrier
and effect-instance parameters. All recognized recursive APIs take fuel as
their first explicit natural parameter. -/
def fuelArgument? (e : Expr) : MetaM (Option Expr) := do
  let mut ty ← inferType e.getAppFn
  for arg in e.getAppArgs do
    ty ← whnf ty
    match ty with
    | .forallE _ dom body bi =>
      if bi.isExplicit && (← whnf dom).isConstOf ``Nat then return some arg.consumeMData
      ty := body.instantiate1 arg
    | _ => return none
  return none

/-- The fuel argument of an interpreter call on a variable fuel in head
position: the head itself, the discriminant of a `match` or the condition
of an `if` at the head, the argument of an option lift, or the body of a
`mapM` at the head. Not inside the alternatives of a match or a
continuation: a split there would copy the whole proof into a zero
branch that does not diverge. -/
partial def stuckFuel (head : Expr) : MetaM (Option FVarId) := do
  let e := head.consumeMData
  let here : Option FVarId ← match e.getAppFn.consumeMData with
    | .const c _ =>
      if (blockFunctions.contains c || invocations.contains c) &&
          e.getAppNumArgs ≥ 1 then
        match ← fuelArgument? e with
        | some (.fvar f) => pure (some f)
        | _ => pure none
      else pure none
    | _ => pure none
  if let some f := here then return some f
  if let some app ← matchMatcherApp? e then
    for d in app.discrs do
      if let some f ← stuckFuel d then return some f
    return none
  if e.isAppOfArity ``ite 5 then return ← stuckFuel (e.getArg! 1)
  if e.isAppOfArity ``P4SpecTec.Prelude.Eval.ofOption 3 then return ← stuckFuel (e.getArg! 2)
  if e.isAppOfArity ``P4SpecTec.Prelude.Eval.err? 2 then return ← stuckFuel (e.getArg! 1)
  if e.isAppOf ``List.mapM && e.getAppNumArgs ≥ 2 then
    -- the body of the iteration
    let f := (e.getArg! (e.getAppNumArgs - 2)).consumeMData
    match f with
    | .lam _ _ b _ => return ← stuckFuel b
    | _ => return ← stuckFuel f
  if e.isAppOf ``List.foldlM && e.getAppNumArgs ≥ 3 then
    let f := (e.getArg! (e.getAppNumArgs - 3)).consumeMData
    match f with
    | .lam _ _ b _ =>
      match b with
      | .lam _ _ b' _ => return ← stuckFuel b'
      | _ => return ← stuckFuel b
    | _ => return ← stuckFuel f
  return none

/-- The generated variable on the right side of a fact, to be split: the
right side mentions only generated data (`toValue` of generated values,
maps of it over generated lists), so any variable in it, the last
argument first, is one. -/
partial def generatedVar (e : Expr) : Option FVarId :=
  match e.consumeMData with
  | .fvar f => some f
  | .app .. => (e.consumeMData.getAppArgs).reverse.findSome? generatedVar
  | _ => none

/-- Whether a variable is of a generated type (or a container of one),
and not of a type of the interpreter's runtime. -/
def isGeneratedVar (lib : Name) (v : FVarId) : MetaM Bool := do
  let ty ← whnfR (← v.getType)
  let runtime := (ty.find? fun e => match e with
    | .const c _ => (`P4SpecTec.Lang).isPrefixOf c || (`P4SpecTec.Util).isPrefixOf c ||
        (`P4SpecTec.Runtime).isPrefixOf c || (`P4SpecTec.Interp_al).isPrefixOf c ||
        (`P4SpecTec.Domain).isPrefixOf c
    | _ => false).isSome
  if runtime then return false
  match ty.getAppFn with
  | .const c _ =>
    pure (lib.isPrefixOf c || c == ``Bool || c == ``List || c == ``Option || c == ``Prod ||
      c == ``Nat || c == ``Int || c == ``String)
  | _ => pure false

/-- The interpreter value the head is stuck on: the first variable of a
`match` discriminant or an `if` condition, with the generated variable
its fact relates it to. -/
def stuckOn (head : Expr) : TacticM (Option FVarId) := timed "stuckOn" do
  (← getMainGoal).withContext do
    -- every match and `if` inside the head, outermost first
    let mut candidates : Array Expr := #[]
    let mut todo : List Expr := [head]
    let mut fuel := 10000
    while fuel > 0 do
      fuel := fuel - 1
      match todo with
      | [] => break
      | e :: rest =>
        todo := rest
        let e := e.consumeMData
        -- only matches: an `if` tests values, it does not inspect their shape
        if let some app ← matchMatcherApp? e then
          candidates := candidates ++ app.discrs
        match e with
        | .app f a => todo := f :: a :: todo
        | .lam _ _ b _ | .forallE _ _ b _ => todo := b :: todo
        | .letE _ _ v b _ => todo := v :: b :: todo
        | .proj _ _ x => todo := x :: todo
        | _ => pure ()
    let mut vars : Array FVarId := #[]
    for d in candidates do
      let ((), st) ← ((← instantiateMVars d).collectFVars).run {}
      for f in st.fvarIds do
        unless vars.contains f do vars := vars.push f
    traceStep m!"stuck on {vars.toList.map Expr.fvar}"
    -- the fact about a stuck variable names the generated variable to split
    for v in vars do
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let ty := (← instantiateMVars decl.type).consumeMData
        if let some (_, lhs, rhs) := ty.eq? then
          let lhs := lhs.consumeMData
          if lhs.isApp && (lhs.getArg! (lhs.getAppNumArgs - 1)).consumeMData == .fvar v then
            if let some g := generatedVar rhs then return some g
    -- a variable of a generated type in the discriminant itself; a list's shape first, as
    -- splitting its elements first would repeat the shape split in every element case
    let lib ← libOf
    for v in vars do
      if (← isGeneratedVar lib v) && (← whnfR (← v.getType)).isAppOf ``List then
        return some v
    for v in vars do
      if ← isGeneratedVar lib v then return some v
    pure none

/-! ## Facts -/

/-- The `HoldsSpec` hypothesis and the spec it names. -/
def specHyp : TacticM (Option (Name × Name)) := do
  (← getMainGoal).withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if ty.isAppOfArity ``HoldsSpec 2 then
        if let .const spec _ := (ty.getArg! 0).consumeMData.getAppFn.consumeMData then
          return some (decl.userName, spec)
    pure none

/-- The quoted definition constants of the spec definitions named `id` that
the library has: `Lib.id.al` for a relation or type, `Lib.«$id».al` for a
function. A type and a function may share a name (Nano's `id`), and a lookup
string does not say which table it reads, so every candidate is returned. -/
def quotedOf (lib : Name) (id : String) : MetaM (List Name) := do
  let env ← getEnv
  let candidates := [Name.str (Name.str lib id) "al", Name.str (Name.str lib ("$" ++ id)) "al"]
  pure (candidates.filter env.contains)

/-- The string literals looked up in the global tables inside `e`. -/
partial def tableLookups (e : Expr) : List String :=
  let e := e.consumeMData
  let here := if e.isAppOf ``Std.HashMap.get? && e.getAppNumArgs ≥ 2 then
      match (e.getArg! (e.getAppNumArgs - 1)).consumeMData with
      | .lit (.strVal s) => [s]
      | _ => []
    else []
  here ++ (match e with
    | .app f a => tableLookups f ++ tableLookups a
    | .lam _ t b _ | .forallE _ t b _ => tableLookups t ++ tableLookups b
    | .letE _ t v b _ => tableLookups t ++ tableLookups v ++ tableLookups b
    | .mdata _ e => tableLookups e
    | .proj _ _ e => tableLookups e
    | _ => [])

/-- A proof that the constant `q` is a member of the list the constant
`spec` unfolds to: `List.Mem.tail` for every earlier element, then
`List.Mem.head`. -/
def memProof (spec q : Name) : MetaM Expr := do
  let some info := (← getEnv).find? spec | throwError "refine_al: no spec {spec}"
  let some value := info.value? | throwError "refine_al: {spec} has no value"
  let α := mkConst ``P4SpecTec.Lang.Al.def
  let target := mkConst q
  let rec go (l : Expr) (fuel : Nat) : MetaM Expr := do
    match fuel with
    | 0 => throwError "refine_al: {q} is not in {spec}"
    | fuel + 1 =>
      let l := l.consumeMData
      if l.isAppOfArity ``List.cons 3 then
        let a := l.getArg! 1
        let as := l.getArg! 2
        if a.consumeMData.isConstOf q then
          pure (mkAppN (mkConst ``List.Mem.head [Level.zero]) #[α, target, as])
        else
          pure (mkAppN (mkConst ``List.Mem.tail [Level.zero]) #[α, target, a, as, ← go as fuel])
      else throwError "refine_al: {q} is not in {spec}"
  go value 100000

/-- Derive the table facts for every definition the goal looks up, from
the `HoldsSpec` hypothesis; `true` when a new fact was added. -/
def tableFacts (lib : Name) : TacticM Bool := timed "tableFacts" do
  let some (hspec, spec) ← specHyp | pure false
  let goal ← getMainGoal
  let lookups ← goal.withContext do
    pure (tableLookups (← instantiateMVars (← goal.getType))).eraseDups
  let mut added := false
  let quoted ← lookups.flatMapM fun id => (quotedOf lib id : TacticM _)
  for q in quoted do
    let h := Name.mkSimple s!"rf_tbl_{q.getPrefix.getString!}"
    if ← (← getMainGoal).withContext do pure ((← getLCtx).findFromUserName? h).isSome then
      continue
    let g ← getMainGoal
    let g' ← g.withContext do
      let hs ← fvarOf hspec
      let mem ← memProof spec q
      let val := mkApp2 (.fvar hs) (mkConst q) mem
      let ty ← inferType val
      let g' ← g.assert h ty val
      let (_, g') ← g'.intro1P
      pure g'
    setGoals [g']
    let _ ← tryTac (evalTactic (← `(tactic| simp only [Holds, $(mkIdent q):ident, Q.d_it, Q.i_it]
      at $(mkIdent h):ident)))
    added := true
  pure added

/-- Expose the shapes the facts determine: every hypothesis
`canon v = ⟨q, n, r⟩` becomes `v.it = ...`, and the lists and mixfixes
inside are destructured, until nothing applies. -/
partial def expose : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let goal ← getMainGoal
  let hyps ← goal.withContext do
    let mut out : Array (Name × Name) := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if let some (_, lhs, rhs) := ty.eq? then
        let lhs := lhs.consumeMData
        let rhs := rhs.consumeMData
        let lemma? : Option Name :=
          if lhs.isAppOfArity ``P4SpecTec.Refine.canon 1 &&
              rhs.isAppOfArity ``P4SpecTec.Util.Source.info.mk 6 then
            some ``canon_eq_it
          else if lhs.isAppOfArity ``canon' 1 then
            match rhs.getAppFn.consumeMData with
            | .const c _ =>
              if c == ``P4SpecTec.Lang.Il.value'.BoolV then some ``canon'_eq_bool
              else if c == ``P4SpecTec.Lang.Il.value'.NumV then some ``canon'_eq_num
              else if c == ``P4SpecTec.Lang.Il.value'.TextV then some ``canon'_eq_text
              else if c == ``P4SpecTec.Lang.Il.value'.StructV then some ``canon'_eq_struct
              else if c == ``P4SpecTec.Lang.Il.value'.CaseV then some ``canon'_eq_case
              else if c == ``P4SpecTec.Lang.Il.value'.TupleV then some ``canon'_eq_tuple
              else if c == ``P4SpecTec.Lang.Il.value'.ListV then some ``canon'_eq_list
              else if c == ``P4SpecTec.Lang.Il.value'.ExternV then some ``canon'_eq_extern
              else if c == ``P4SpecTec.Lang.Il.value'.OptV then
                match (rhs.getArg! 0).consumeMData.getAppFn.consumeMData with
                | .const ``Option.none _ => some ``canon'_eq_none
                | .const ``Option.some _ => some ``canon'_eq_some
                | _ => none
              else none
            | _ => none
          else if lhs.isAppOfArity ``canons 1 then
            if rhs.isAppOfArity ``List.nil 1 then some ``canons_eq_nil
            else if rhs.isAppOfArity ``List.cons 3 then some ``canons_eq_cons
            else none
          else if lhs.isAppOfArity ``canonFields 1 then
            if rhs.isAppOfArity ``List.nil 1 then some ``canonFields_eq_nil
            else if rhs.isAppOfArity ``List.cons 3 &&
                (rhs.getArg! 1).consumeMData.isAppOfArity ``Prod.mk 4 then
              some ``canonFields_eq_cons
            else none
          else if lhs.isAppOfArity ``canonMixfix 1 then
            match rhs.getAppFn.consumeMData with
            | .const c _ =>
              if c == ``P4SpecTec.Domain.Mixfix.t.Arg then some ``canonMixfix_eq_arg
              else if c == ``P4SpecTec.Domain.Mixfix.t.Atom then some ``canonMixfix_eq_atom
              else if c == ``P4SpecTec.Domain.Mixfix.t.Brack then some ``canonMixfix_eq_brack
              else if c == ``P4SpecTec.Domain.Mixfix.t.Infix then some ``canonMixfix_eq_infix
              else if c == ``P4SpecTec.Domain.Mixfix.t.Seq then some ``canonMixfix_eq_seq
              else none
            | _ => none
          else if lhs.isAppOfArity ``canonMixfixes 1 then
            if rhs.isAppOfArity ``List.nil 1 then some ``canonMixfixes_eq_nil
            else if rhs.isAppOfArity ``List.cons 3 then some ``canonMixfixes_eq_cons
            else none
          else none
        if let some l := lemma? then out := out.push (decl.userName, l)
    pure out
  if hyps.isEmpty then return
  for (h, l) in hyps do
    -- a contradictory fact closes the goal on the way
    if (← getGoals).isEmpty then return
    let h' ← freshName "rf_h"
    -- the lemma's conclusion is an equation or an existential; destructure fully
    let ok ← timed "expose.have" (tryTac (evalTactic (← `(tactic| have $(mkIdent h'):ident :=
      $(mkIdent l):ident $(mkIdent h):ident))))
    if ok then
      let _ ← timed "expose.clear" (tryTac (evalTactic (← `(tactic| clear $(mkIdent h):ident))))
      destructure h'
  expose
where
  /-- Split existentials and conjunctions, substitute equations on variables. -/
  destructure (h : Name) : TacticM Unit := do
    if (← getGoals).isEmpty then return
    let hid ← fvarOf h
    let ty ← typeOf hid
    let ty := (← (← getMainGoal).withContext (whnfR ty)).consumeMData
    if ty.isAppOfArity ``Exists 2 then
      let x ← freshName "rf_v"
      let h' ← freshName "rf_h"
      timed "expose.obtain" (evalTactic (← `(tactic|
        obtain ⟨$(mkIdent x):ident, $(mkIdent h'):ident⟩ := $(mkIdent h):ident)))
      destructure h'
    else if ty.isAppOfArity ``And 2 then
      let h1 ← freshName "rf_h"
      let h2 ← freshName "rf_g"
      timed "expose.obtain" (evalTactic (← `(tactic|
        obtain ⟨$(mkIdent h1):ident, $(mkIdent h2):ident⟩ := $(mkIdent h):ident)))
      destructure h1
      destructure h2
    else if let some (_, lhs, rhs) := ty.eq? then
      -- `canon v' = w` stays a fact; `vs = v :: vs'` substitutes; `v.it = C ...`
      -- destructures `v`, so that the payload is substituted and every
      -- `match` on it computes
      let lhs := lhs.consumeMData
      let projected : Option FVarId := match lhs with
        | .proj _ _ (.fvar x) => some x
        | _ =>
          if lhs.isAppOfArity ``P4SpecTec.Util.Source.info.it 4 then
            match (lhs.getArg! 3).consumeMData with
            | .fvar x => some x
            | _ => none
          else none
      if lhs.isFVar then
        let _ ← timed "expose.subst" (tryTac (evalTactic (← `(tactic| subst $(mkIdent h):ident))))
      else if rhs.consumeMData.isFVar then
        let _ ← timed "expose.subst" (tryTac (evalTactic (← `(tactic| subst $(mkIdent h):ident))))
      else if let some x := projected then
        let xn ← (← getMainGoal).withContext do pure (← x.getDecl).userName
        let cased ← timed "expose.cases"
          (tryTac (evalTactic (← `(tactic| cases $(mkIdent xn):ident))))
        if cased then
          let _ ← timed "expose.dsimp"
            (tryTac (evalTactic (← `(tactic| dsimp only at $(mkIdent h):ident))))
          let _ ← timed "expose.subst" (tryTac (evalTactic (← `(tactic| subst $(mkIdent h):ident))))

end P4SpecTec.Tactic
