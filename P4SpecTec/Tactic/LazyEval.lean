import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Omega
import Lean.Meta.Check
import Lean.Meta.Eqns
import Lean.Meta.Tactic.Delta
import Lean.Meta.Transform
import Lean.Util.ForEachExpr

/-!
# Lazy evaluation of generated code with kernel-checked proofs

`lazy_eval` proves `lhs = rhs` by evaluating `lhs`. Generated recursive functions are
`partial_fixpoint` definitions, which neither `decide` nor the kernel can reduce, and library
functions defined by well-founded recursion reduce in the kernel only through accessibility
proofs, whose cost can be exponential. The evaluator therefore splits the work:

* Meta-level `whnf` performs every definitional step of non-recursive code: beta, matchers,
  projections, instances and literal arithmetic. The kernel re-checks these steps, which is
  cheap because they are the same reductions.
* A definition that *reaches* a fixpoint (is one, or unfolds to code that mentions one) is
  never unfolded silently. It is marked irreducible for the evaluation and rewritten by its
  unfolding equation (`eq_def`), an explicit proof step. Rules supplied by the caller rewrite
  their heads the same way, with conditions discharged by evaluation.
* A stuck position (a matcher discriminant, a recursor major premise, a projected structure
  or a strict argument) is evaluated separately and replaced by congruence, abstracting all
  its syntactic occurrences so that dependent types stay correct.
* Between two proof steps the kernel must re-derive the definitional gap. Every reaching
  constant occurring on both sides of the gap is abstracted into a variable, so the kernel
  cannot unfold a fixpoint while checking it: its lazy delta heuristic would otherwise unfold
  the higher well-founded definition first.

Evaluation is call by value: the fields of a computed constructor application are evaluated
before it is substituted, so shared results are not recomputed. Free variables of the goal are
replaced by temporary axioms during evaluation, inside `withoutModifyingEnv`: Meta folds
natural-number arithmetic only on terms without free variables, and the kernel never unfolds
an axiom, so the proof is valid with the variables put back. Stuck symbolic terms remain in the
result. Natural-number operations the kernel evaluates natively are kept folded when an
argument is symbolic.

Arguments of `lazy_eval [...]` that are equations are rules; other propositions are facts. When
evaluation is stuck on a Boolean or decidable test about symbolic values that all occur in the
facts, the test is put in arithmetic normal form and `omega` tries to decide it from the facts;
a decision replaces the test by congruence. `lazy_eval% t` elaborates to the evaluated value of
`t`, so that a result can be named once and reused through a rule. The trace class
`lazy_eval` reports rule mismatches and decision attempts.

Not an upstream mirror: this is proof support of our own.
-/

namespace P4SpecTec.Tactic.LazyEval

open Lean Meta Elab Tactic

initialize registerTraceClass `lazy_eval

/-- Natural-number operations the kernel evaluates natively on literals (GMP), whatever their
logical definition. They are never rewritten, and are frozen for symbolic arguments. -/
def kernelNatOps : List Name :=
  [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.gcd, ``Nat.beq, ``Nat.ble,
   ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``Nat.pow, ``Nat.log2]

/-- The evaluation context: rewrite rules, their head constants, and facts. -/
structure Context where
  /-- Proofs of `∀ xs, conditions → lhs = rhs`, each condition an equation `a = b`. -/
  rules : Array Expr := #[]
  /-- The head constants of the rules' left-hand sides; never unfolded silently. -/
  ruleHeads : Array Name := #[]
  /-- Arithmetic facts that decide stuck Boolean and decidable tests, through `omega`. -/
  facts : Array Expr := #[]
  /-- The temporary axioms standing for free variables: symbolic atoms, never folded. -/
  atoms : Array Name := #[]

/-- Evaluation state: caches and a step budget. -/
structure State where
  /-- Whether a constant reaches a fixpoint. -/
  reach : Std.HashMap Name Bool := {}
  /-- Deep evaluation results, with their proofs. -/
  cache : Std.HashMap Expr (Expr × Option Expr) := {}
  /-- Rewrite steps taken. -/
  steps : Nat := 0
  /-- The maximum number of rewrite steps. -/
  budget : Nat := 1000000

/-- The evaluation monad; tactics decide stuck tests. -/
abbrev EvalM := ReaderT Context (StateRefT State Term.TermElabM)

/-- A definition that is irreducible and has an unfolding equation: well-founded or
`partial_fixpoint` recursion. -/
def isFixpoint (c : Name) : MetaM Bool := do
  unless (← getReducibilityStatus c) matches .irreducible do return false
  let some (.defnInfo _) := (← getEnv).find? c | return false
  return (← getUnfoldEqnFor? c (nonRec := true)).isSome

/-- Whether unfolding `c` can expose a fixpoint. Such constants, and the rule heads, are only
rewritten by explicit equations. -/
partial def reaches (c : Name) : EvalM Bool := do
  if kernelNatOps.contains c then return false
  if let some b := (← get).reach[c]? then return b
  if (← read).ruleHeads.contains c then
    modify fun s => { s with reach := s.reach.insert c true }
    return true
  -- a provisional answer breaks cycles through recursive definitions
  modify fun s => { s with reach := s.reach.insert c false }
  let b ← if ← isFixpoint c then pure true else
    match (← getEnv).find? c with
    | some (.defnInfo d) => d.value.getUsedConstants.anyM reaches
    | _ => pure false
  modify fun s => { s with reach := s.reach.insert c b }
  return b

/-- Whether `e` mentions a reaching constant. -/
def mentionsReaching (e : Expr) : EvalM Bool :=
  e.getUsedConstants.anyM reaches

/-- Mark every reaching constant of `e` irreducible, so that `whnf` stops at it. The caller
runs inside `withoutModifyingEnv`, which restores the attributes. -/
def freeze (e : Expr) : EvalM Unit := do
  let mut changed := false
  for c in e.getUsedConstants do
    unless ← reaches c do continue
    unless (← getReducibilityStatus c) matches .irreducible do
      setReducibilityStatus c .irreducible
      changed := true
  if changed then modifyThe Meta.State fun st => { st with cache := {} }

/-- The value of a natural-number term, through successor chains and literal sums. -/
partial def natValue? (t : Expr) (depth : Nat := 0) : MetaM (Option Nat) := do
  if depth > 100000 then return none
  let w ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxRecDepth := 2000 }) (whnf t))
    fun _ => pure t
  if let some n := w.rawNatLit? then return some n
  if let some n := w.nat? then return some n
  if w.isAppOfArity ``Nat.succ 1 then
    return (← natValue? w.appArg! (depth + 1)).map (· + 1)
  if w.isAppOfArity ``HAdd.hAdd 6 then
    if let some a ← natValue? (w.getArg! 4) (depth + 1) then
      if let some b ← natValue? (w.getArg! 5) (depth + 1) then return some (a + b)
  return none

/-- Replace natural-number subterms that mention free variables yet have a value by that
literal: Meta folds arithmetic only on closed terms and otherwise recurses in unary. -/
def groundNats (e : Expr) : MetaM Expr := do
  let nat := mkConst ``Nat
  Meta.transform e (post := fun t => do
    unless t.isApp && t.hasFVar && !t.hasLooseBVars do return .done t
    unless ← isDefEq (← inferType t) nat do return .done t
    match ← natValue? t with
    | some n => return .done (mkNatLit n)
    | none => return .done t)

/-- `whnf` that recovers from unary natural-number recursion by reducing step by step and
grounding natural-number subterms in between. -/
partial def whnfSafe (e : Expr) (fuel : Nat := 400) : MetaM Expr := do
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxRecDepth := 8000 }) (whnf e))
    fun ex => do
      if fuel == 0 then throw ex
      let e₁ ← groundNats (← whnfCore e)
      if e₁ != e then return ← whnfSafe e₁ (fuel - 1)
      match ← unfoldDefinition? e₁ with
      | some e₂ => whnfSafe (← groundNats (← whnfCore e₂)) (fuel - 1)
      | none => throw ex

/-- Whether `e` is a value for evaluation purposes: a literal, binder, sort or constructor
application. -/
def isValue (e : Expr) : MetaM Bool := do
  if e.isLit || e.isLambda || e.isSort || e.isForall then return true
  match e.getAppFn with
  | .const c _ => return (← getEnv).isConstructor c
  | _ => return false

/-- The reaching constant occurrences, with their levels, occurring in both `b` and `b'`. -/
def sharedReaching (b b' : Expr) : EvalM (Array Expr) := do
  let occurrences (e : Expr) : EvalM (Array Expr) := do
    unless ← mentionsReaching e do return #[]
    let found ← IO.mkRef (#[] : Array Expr)
    e.forEach fun t => do
      if let .const n _ := t then
        if ← reaches n then
          unless (← found.get).contains t do found.modify (·.push t)
    found.get
  let left ← occurrences b
  if left.isEmpty then return #[]
  let right ← occurrences b'
  return left.filter right.contains

/-- `Eq.trans` without `mkEqTrans`'s removal of reflexivity proofs, which would drop the
anchors that state a definitional gap. -/
def mkTrans (h₁ h₂ : Expr) : MetaM Expr := do
  let some (α, a, b) := (← inferType h₁).eq? | throwError "lazy_eval: not an equation {h₁}"
  let some (_, _, c) := (← inferType h₂).eq? | throwError "lazy_eval: not an equation {h₂}"
  return mkApp6 (mkConst ``Eq.trans [← getLevel α]) α a b c h₁ h₂

/-- Compose two optional steps. A definitional gap between them is stated with every shared
reaching constant abstracted, when that is type-correct, so the kernel cannot unfold a
fixpoint while checking it. -/
def compose (p q : Option Expr) : EvalM (Option Expr) := do
  let (some p, some q) := (p, q) | return p <|> q
  let some (_, _, b) := (← inferType p).eq? | throwError "lazy_eval: not an equation {p}"
  let some (_, b', _) := (← inferType q).eq? | throwError "lazy_eval: not an equation {q}"
  if b == b' then return some (← mkTrans p q)
  let b ← instantiateMVars b
  let b' ← instantiateMVars b'
  let cs ← sharedReaching b b'
  if cs.isEmpty then return some (← mkTrans p q)
  let names ← cs.mapIdxM fun k c => return ((`g).appendIndexAfter k, ← inferType c)
  let gap? ← withLocalDeclsDND names fun gs => do
    let abstract (e : Expr) := e.replace fun t => (cs.idxOf? t).map (gs[·]!)
    let eq ← mkEq (abstract b) (abstract b')
    -- abstraction is sound only where no type mentions the abstracted constants
    unless ← isTypeCorrect (← mkForallFVars gs eq) do return none
    let body := mkApp2 (mkConst ``id [Level.zero]) eq (← mkEqRefl (abstract b))
    return some (← mkLambdaFVars gs body)
  match gap? with
  | some gap => return some (← mkTrans (← mkTrans p (mkAppN gap cs)) q)
  | none => return some (← mkTrans p q)

/-- Proof of `e = e[s := s']` from `ps : s = s'`, abstracting every syntactic occurrence of
`s`, including those in types. -/
def congrAll (e s s' ps : Expr) : MetaM Expr := do
  let α ← inferType s
  let β ← inferType e
  let motive ← withLocalDeclD `x α fun x =>
    mkLambdaFVars #[x] (e.replace fun t => if t == s then some x else none)
  return mkApp6 (mkConst ``congrArg [← getLevel α, ← getLevel β]) α β s s' motive ps

/-- Count a rewrite step against the budget. -/
def step : EvalM Unit := do
  modify fun s => { s with steps := s.steps + 1 }
  if (← get).steps > (← get).budget then
    throwError "lazy_eval: step budget {(← get).budget} exhausted"

/-- Rewrite the head of `e` by a rule, discharging conditions with `evalCond`. -/
def ruleStep? (evalCond : Expr → EvalM (Expr × Option Expr)) (e : Expr) (c : Name) :
    EvalM (Option (Expr × Expr)) := do
  for rule in (← read).rules do
    let (ms, _, body) ← forallMetaTelescopeReducing (← inferType rule)
    let some (_, lhs, rhs) := body.eq? | continue
    unless lhs.getAppFn.isConstOf c do continue
    unless ← isDefEq lhs e do
      trace[lazy_eval] "rule {rule} does not match{indentExpr e}"
      continue
    let mut ok := true
    -- conditions assign the remaining variables, in order
    for m in ms do
      if ← m.mvarId!.isAssigned then continue
      let ty ← instantiateMVars (← m.mvarId!.getType)
      unless ← isProp ty do continue
      let some (_, a, b) := ty.eq? | ok := false; break
      freeze a
      let (v, pv) ← evalCond a
      unless ← isDefEq v b do ok := false; break
      let b ← instantiateMVars b
      let pv ← match pv with | some pv => pure pv | none => mkEqRefl a
      let some pab ← compose (some pv) (some (← mkEqRefl b)) | ok := false; break
      m.mvarId!.assign pab
    for m in ms do
      unless ← m.mvarId!.isAssigned do ok := false
    unless ok do continue
    step
    let rhs ← instantiateMVars rhs
    freeze rhs
    return some (rhs, ← instantiateMVars (mkAppN rule ms))
  return none

/-- One rewrite at the head of `e`: a rule, or the unfolding equation of a reaching
definition. -/
def rewriteHead? (evalCond : Expr → EvalM (Expr × Option Expr)) (e : Expr) :
    EvalM (Option (Expr × Expr)) := do
  let .const c us := e.getAppFn | return none
  if (← read).ruleHeads.contains c then
    if let some r ← ruleStep? evalCond e c then return some r
  unless ← reaches c do return none
  let some eqn ← getUnfoldEqnFor? c (nonRec := true) | return none
  let arity ← forallTelescope (← getConstInfo eqn).type fun xs _ => pure xs.size
  let args := e.getAppArgs
  if args.size < arity then return none
  let mut h := mkAppN (mkConst eqn us) args[:arity]
  let some (_, _, rhs) := (← inferType h).eq? | return none
  let mut rhs := rhs
  for a in args[arity:] do
    h ← mkCongrFun h a
    rhs := mkApp rhs a
  step
  let body := rhs.headBeta
  freeze body
  return some (body, h)

/-- The integer value of a closed integer term, through `Int.ofNat`, negation and literals. -/
def intValue? (t : Expr) : MetaM (Option Int) := do
  if t.hasFVar || t.hasMVar then return none
  let w ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxRecDepth := 2000 }) (whnf t))
    fun _ => pure t
  if w.isAppOfArity ``Int.ofNat 1 then return (← natValue? w.appArg!).map Int.ofNat
  if w.isAppOfArity ``Int.negSucc 1 then
    return (← natValue? w.appArg!).map fun n => Int.negSucc n
  return none

/-- A definitionally equal form of a test that `omega` reads: arithmetic on the natural numbers
with the usual operators, closed subterms folded to literals, and byte values as `toNat`. -/
def arithNormalize (e : Expr) (isAtom : Name → Bool) : MetaM Expr := do
  let nat := mkConst ``Nat
  let int := mkConst ``Int
  Meta.transform e (post := fun t => do
    -- closed natural and integer subterms: their literal
    unless t.hasLooseBVars || (t.find? fun u => u.isFVar || (u.constName?.any isAtom)).isSome do
      if t.isApp && !t.isAppOfArity ``OfNat.ofNat 3 then
        let ty ← whnfR (← inferType t)
        if ty == nat then
          if let some n ← natValue? t then return .done (mkNatLit n)
        if ty == int then
          if let some i ← intValue? t then return .done (toExpr i)
    let binary (op : Name) := do
      return .done (← mkAppM op #[t.getArg! 0, t.getArg! 1])
    if t.isAppOfArity ``Nat.mod 2 then return ← binary ``HMod.hMod
    if t.isAppOfArity ``Nat.div 2 then return ← binary ``HDiv.hDiv
    if t.isAppOfArity ``Nat.add 2 then return ← binary ``HAdd.hAdd
    if t.isAppOfArity ``Nat.sub 2 then return ← binary ``HSub.hSub
    if t.isAppOfArity ``Nat.mul 2 then return ← binary ``HMul.hMul
    if t.isAppOfArity ``Fin.val 2 then
      let f := t.getArg! 1
      if f.isAppOfArity ``BitVec.toFin 2 && (f.getArg! 1).isAppOfArity ``UInt8.toBitVec 1 then
        return .done (mkApp (mkConst ``UInt8.toNat) (f.getArg! 1).appArg!)
    return .done t)

/-- Prove `target` from the facts: normalize Boolean and decidable forms, then `omega`. -/
def closeByFacts (target : Expr) : EvalM (Option Expr) := do
  let facts := (← read).facts
  -- prove `fact₁ → … → target`, then apply it to the facts
  let statement ← facts.foldrM (init := target) fun f acc => do
    return mkForall `h .default (← inferType f) acc
  let goal ← mkFreshExprMVar statement
  let tac ← `(tactic| (
    intros
    first
      | decide
      | (simp only [Nat.beq_eq, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
          decide_eq_false_iff_not, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
          Bool.not_eq_false', Nat.beq_eq_true_eq, Int.ofNat_eq_natCast, Int.natCast_inj,
          Int.natCast_emod, Int.natAbs_natCast, Int.toNat_natCast, BitVec.val_toFin,
          UInt8.toNat_toBitVec] at *
         omega)
      | omega))
  let saved ← (saveState : Term.TermElabM Term.SavedState)
  let before ← getEnv
  try
    let remaining ← Tactic.run goal.mvarId! (Tactic.evalTactic tac)
    unless remaining.isEmpty do
      saved.restore
      return none
    -- the tactics may add auxiliary lemmas, which the evaluation's environment discards
    let mut proof ← instantiateMVars goal
    let mut changed := true
    while changed do
      changed := false
      for c in proof.getUsedConstants do
        if before.contains c then continue
        let info ← getConstInfo c
        let some v := info.value? (allowOpaque := true)
          | throwError "lazy_eval: no value for {c}"
        proof := proof.replace fun u => match u with
          | .const n us => if n == c then some (v.instantiateLevelParams info.levelParams us)
            else none
          | _ => none
        changed := true
    return some (mkAppN proof facts)
  catch ex =>
    trace[lazy_eval] "not decided: {target}: {ex.toMessageData}"
    saved.restore
    return none

/-- Decide a stuck test `t`, a Boolean or a `Decidable` instance, from the facts: the value
and a proof that `t` equals it. -/
def decideStuck? (t : Expr) : EvalM (Option (Expr × Expr)) := do
  if (← read).facts.isEmpty then return none
  -- only tests about the facts' symbolic atoms can be decided by them
  let atoms := (← read).atoms
  let factAtoms ← (← read).facts.foldlM (init := ({} : NameSet)) fun s f => do
    return (← inferType f).getUsedConstants.foldl (fun s c => if atoms.contains c then s.insert c
      else s) s
  let testAtoms := t.getUsedConstants.filter atoms.contains
  if testAtoms.isEmpty || !testAtoms.all factAtoms.contains then return none
  let ty ← whnfR (← inferType t)
  trace[lazy_eval] "deciding {t} : {ty}"
  let t' ← arithNormalize t atoms.contains
  if ty.isConstOf ``Bool then
    for b in [mkConst ``Bool.true, mkConst ``Bool.false] do
      if let some h ← closeByFacts (← mkEq t' b) then
        return some (b, ← mkExpectedTypeHint h (← mkEq t b))
    return none
  if ty.isAppOfArity ``Decidable 1 then
    let prop := ty.appArg!
    let prop' ← arithNormalize prop atoms.contains
    if let some h ← closeByFacts prop' then
      let v := mkApp2 (mkConst ``Decidable.isTrue) prop h
      return some (v, ← mkAppM ``Subsingleton.elim #[t, v])
    if let some h ← closeByFacts (mkNot prop') then
      let v := mkApp2 (mkConst ``Decidable.isFalse) prop h
      return some (v, ← mkAppM ``Subsingleton.elim #[t, v])
  return none

/-- The stuck tests along the chain blocking `e`, outermost first; nodes are original
subterms. -/
partial def stuckChain (e : Expr) (depth : Nat := 0) : MetaM (List Expr) := do
  if depth > 500 then return []
  let w ← whnfSafe e
  if let .proj _ _ a := w.getAppFn then return e :: (← stuckChain a (depth + 1))
  let some c := w.getAppFn.constName? | return [e]
  let args := w.getAppArgs
  let positions : Array Nat ← do
    if let some info ← getMatcherInfo? c then
      pure (Array.range' info.getFirstDiscrPos info.numDiscrs)
    else if let some (.recInfo r) := (← getEnv).find? c then
      pure #[r.getMajorIdx]
    else pure #[]
  for i in positions do
    if h : i < args.size then
      unless ← isValue (← whnfSafe args[i]) do
        return e :: (← stuckChain args[i] (depth + 1))
  return [e]

/-- The path from `e` to a subterm whose weak head normal form has a rewritable head, through
the positions blocking `e`'s weak head normal form. Nodes are original subterms. A matcher
stuck inside its compiled body ends the path; its caller unfolds it. -/
partial def findPath (e : Expr) : EvalM (Option (List Expr)) := do
  let w ← whnfSafe e
  if let .const c _ := w.getAppFn then
    if ← reaches c then return some [e]
  if let .proj _ _ a := w.getAppFn then
    let some path ← findPath a | return none
    return some (e :: path)
  if ← isValue w then return none
  let .const c _ := w.getAppFn | return none
  let args := w.getAppArgs
  let positions : Array Nat ← do
    if let some info ← getMatcherInfo? c then
      pure (Array.range' info.getFirstDiscrPos info.numDiscrs)
    else if let some (.recInfo r) := (← getEnv).find? c then
      pure #[r.getMajorIdx]
    else pure (Array.range args.size)
  for i in positions do
    if h : i < args.size then
      let a := args[i]
      if ← isValue (← whnfSafe a) then continue
      unless ← mentionsReaching a do continue
      if let some path ← findPath a then
        return some (e :: path)
  if (← getMatcherInfo? c).isSome then return some [e]
  return none

/-- Whether `s` occurs syntactically in `e`. -/
def occurs (s e : Expr) : Bool := (e.find? (· == s)).isSome

/-- Evaluate `e` to weak head normal form; with `deep`, also evaluate constructor fields. The
proof, when present, has exactly `e` and the result as its sides. -/
partial def eval (e : Expr) (deep : Bool) : EvalM (Expr × Option Expr) := do
  if e.isLit || e.isFVar || e.isSort then return (e, none)
  if deep then
    if let some r := (← get).cache[e]? then return r
  let mut cur := e
  let mut p : Option Expr := none
  repeat
    cur ← whnfSafe cur
    if let some (rhs, h) ← rewriteHead? (fun a => eval a true) cur then
      p ← compose p (some h)
      cur := rhs
      continue
    let some path ← findPath cur | do
      -- no rewritable redex: decide a stuck test from the facts, outermost first
      let mut decided := false
      let chain ← stuckChain cur
      trace[lazy_eval] "stuck chain: {chain.map fun t => (t.getAppFn, occurs t cur)}"
      for t in chain.drop 1 do
        unless occurs t cur do continue
        if let some (v, h) ← decideStuck? t then
          p ← compose p (some (← congrAll cur t v h))
          cur := cur.replace fun u => if u == t then some v else none
          decided := true
          break
      unless decided do break
      continue
    -- the deepest blocking subterm that still occurs syntactically in `cur`
    let some s := (path.drop 1).reverse.find? (occurs · cur) | do
      -- `cur` is a matcher stuck inside its compiled body: unfold it definitionally
      let some c := cur.getAppFn.constName? | break
      let some u ← delta? cur (· == c) | break
      let u ← whnfCore u
      if u == cur then break
      cur := u
      continue
    let (s', ps) ← eval s true
    let some ps := ps | break
    p ← compose p (some (← congrAll cur s s' ps))
    cur := cur.replace fun t => if t == s then some s' else none
  if deep then
    if let .const c _ := cur.getAppFn then
      if let some (.ctorInfo ci) := (← getEnv).find? c then
        for i in [ci.numParams : cur.getAppNumArgs] do
          let a := cur.getArg! i
          if a.isLit || a.isLambda || a.isSort then continue
          let α ← inferType a
          if (← isProp α) || α.isSort || (← whnf α).isForall then continue
          let (a', pa) ← eval a true
          if a' == a then continue
          if let some pa := pa then
            p ← compose p (some (← congrAll cur a a' pa))
          cur := cur.replace fun t => if t == a then some a' else none
  if let some q := p then
    let some (_, a, _) := (← inferType q).eq? | throwError "lazy_eval: not an equation {q}"
    if a != e then p ← compose (some (← mkEqRefl e)) p
    p ← compose p (some (← mkEqRefl cur))
  if deep then
    modify fun st => { st with cache := st.cache.insert e (cur, p) }
  return (cur, p)

/-- The innermost subterm blocking `e`'s weak head normal form, for diagnostics. -/
partial def innermostStuck (e : Expr) (depth : Nat := 0) : MetaM Expr := do
  let w ← whnfSafe e
  if depth > 500 then return w
  if let .proj _ _ a := w.getAppFn then return ← innermostStuck a (depth + 1)
  let some c := w.getAppFn.constName? | return w
  let args := w.getAppArgs
  let positions : Array Nat ← do
    if let some info ← getMatcherInfo? c then
      pure (Array.range' info.getFirstDiscrPos info.numDiscrs)
    else if let some (.recInfo r) := (← getEnv).find? c then
      pure #[r.getMajorIdx]
    else pure #[]
  for i in positions do
    if h : i < args.size then
      unless ← isValue (← whnfSafe args[i]) do
        return ← innermostStuck args[i] (depth + 1)
  return w

/-- Whether `rule` proves a (universally quantified, conditional) equation. -/
def isEquation (rule : Expr) : MetaM Bool := do
  forallTelescopeReducing (← inferType rule) fun _ body => return body.isEq

/-- The head constant of a rule's left-hand side. -/
def ruleHead (rule : Expr) : MetaM Name := do
  forallTelescopeReducing (← inferType rule) fun _ body => do
    let some (_, lhs, _) := body.eq? | throwError "lazy_eval: rule {rule} is not an equation"
    let some c := lhs.getAppFn.constName? | throwError "lazy_eval: rule {rule} has no head"
    return c

/-- Replace the free variables `xs` of `es` by temporary axioms; the caller runs inside
`withoutModifyingEnv`. Returns the axioms, in order. -/
def axiomatize (xs : Array Expr) : MetaM (Array Expr) := do
  let mut consts := #[]
  for x in xs do
    let decl ← x.fvarId!.getDecl
    let ty := (← instantiateMVars decl.type).replaceFVars (xs.extract 0 consts.size) consts
    if ty.hasFVar then throwError "lazy_eval: {x} has a type depending on other locals"
    let name ← mkFreshUserName (`_lazy_eval ++ decl.userName)
    addDecl (.axiomDecl { name, levelParams := [], type := ty, isUnsafe := false })
    consts := consts.push (mkConst name)
  return consts

/-- The locals that `es` mention, closed under type dependencies, in context order. -/
def usedLocals (es : Array Expr) : MetaM (Array Expr) := do
  let used : FVarIdSet := es.foldl (fun s e => s.union (collectFVars {} e).fvarSet) {}
  let mut xs : Array Expr := (← getLCtx).foldl (init := #[]) fun acc d =>
    if used.contains d.fvarId then acc.push d.toExpr else acc
  let mut changed := true
  while changed do
    changed := false
    for x in xs do
      for y in (collectFVars {} (← inferType x)).fvarSet do
        unless xs.contains (mkFVar y) do
          xs := xs.push (mkFVar y)
          changed := true
  let found := xs
  return (← getLCtx).foldl (init := #[]) fun acc d =>
    if found.contains d.toExpr then acc.push d.toExpr else acc

/-- Evaluate `e` with the rules (equations) and facts (other propositions), its locals replaced
by temporary axioms, and pass the result, mapped back to the locals, to `k`, which runs in the
evaluation's environment with the same context. Unfolding equations realized there are
re-realized afterwards for the returned proof. -/
def withEvaluation {α : Type} (e : Expr) (rules : Array Expr)
    (k : Context → Expr → Option Expr → EvalM α) : Term.TermElabM α := do
  let e ← instantiateMVars e
  let rules ← rules.mapM instantiateMVars
  let xs ← usedLocals (rules.push e)
  let result ← withoutModifyingEnv do
    let consts ← axiomatize xs
    let toConst (e : Expr) := e.replaceFVars xs consts
    let back (e : Expr) := e.replace fun t => (consts.idxOf? t).map (xs[·]!)
    let e' := toConst e
    -- equations are rules; other propositions are facts for deciding stuck tests
    let mut rules' := #[]
    let mut facts := #[]
    for r in rules.map toConst do
      if ← isEquation r then rules' := rules'.push r else facts := facts.push r
    let heads ← rules'.mapM fun r => ruleHead r
    let atoms := consts.filterMap (·.constName?)
    let ctx : Context := { rules := rules', ruleHeads := heads, facts, atoms }
    let run : EvalM α := do
      -- symbolic arithmetic stays folded; Meta still evaluates these on literals
      for c in kernelNatOps do setReducibilityStatus c .irreducible
      freeze e'
      for r in rules' do freeze (← inferType r)
      let (v, p) ← eval e' true
      let v' := back v
      withReader (fun _ => ctx) do
        try k ctx v' (p.map back)
        catch ex =>
          let stuck := back (← innermostStuck v)
          throwError "{ex.toMessageData}\ninnermost stuck subterm:{indentExpr stuck}"
    let (r, _) ← (run.run ctx).run {}
    return r
  modifyThe Meta.State fun st => { st with cache := {} }
  return result

/-- Re-realize the unfolding equations a proof uses, which the evaluation's environment
discarded. -/
def realizeEquations (proof : Expr) : MetaM Unit := do
  for c in proof.getUsedConstants do
    unless (← getEnv).contains c do
      if c.isStr && c.getString! == "eq_def" then
        discard <| getUnfoldEqnFor? c.getPrefix (nonRec := true)
      unless (← getEnv).contains c do
        throwError "lazy_eval: proof uses the unavailable constant {c}"

/-- Evaluate `lhs` and prove `lhs = rhs`, assigning metavariables of `rhs`. -/
def prove (lhs rhs : Expr) (rules : Array Expr) : Term.TermElabM Expr := do
  let proof ← withEvaluation lhs rules fun _ v p => do
    unless ← isDefEq v rhs do
      throwError "lazy_eval: evaluated to{indentExpr v}\nwhich is not{indentExpr rhs}"
    compose p (some (← mkEqRefl (← instantiateMVars rhs)))
  let proof ← match proof with
    | some p => pure p
    | none => mkEqRefl lhs
  realizeEquations proof
  return proof

/-- The evaluated value of a term, for naming a result that later evaluations reuse through an
equation proved by `lazy_eval`. The value must not mention the locals, such as assumptions
that the rules use. -/
def value (e : Expr) (rules : Array Expr) (locals : Array Expr) : Term.TermElabM Expr := do
  let v ← withEvaluation e rules fun _ v _ => pure v
  let v ← instantiateMVars v
  if v.hasMVar || locals.any fun x => v.containsFVar x.fvarId! then
    throwError "lazy_eval%: the value depends on its assumptions{indentExpr v}"
  return v

/-- `lazy_eval% (assuming binders,)? t (using [r₁, …])?` elaborates to the evaluated value of
`t`, evaluated with the rules `rᵢ`, which may mention the assumed binders. -/
syntax (name := lazyEvalTerm)
  "lazy_eval% " ("assuming " bracketedBinder+ ", ")? term (" using " "[" term,* "]")? : term

/-- Elaborate `lazy_eval%`. -/
@[term_elab lazyEvalTerm] def elabLazyEvalTerm : Term.TermElab := fun stx expected? => do
  match stx with
  | `(lazy_eval% $[assuming $bs*,]? $t $[using [$rs,*]]?) =>
    Term.elabBinders (bs.getD #[]) fun locals => do
      let e ← Term.elabTerm t expected?
      let rules ← ((rs.map (·.getElems)).getD #[]).mapM fun r => Term.elabTerm r none
      Term.synthesizeSyntheticMVarsNoPostponing
      value e rules locals
  | _ => Elab.throwUnsupportedSyntax

/-- `lazy_eval [r₁, …]` proves `lhs = rhs` by evaluating `lhs` with the unfolding equations of
recursive definitions and the rules `rᵢ`, proofs of `∀ xs, (a = b) → … → l = r`. -/
syntax (name := lazyEval) "lazy_eval" (" [" term,* "]")? : tactic

/-- Elaborate `lazy_eval`. -/
@[tactic lazyEval] def evalLazyEval : Tactic := fun stx => withMainContext do
  let rules ← match stx with
    | `(tactic| lazy_eval [$rs,*]) => rs.getElems.mapM fun t => elabTerm t none
    | _ => pure #[]
  let goal ← getMainGoal
  let some (_, lhs, rhs) := (← whnfR (← goal.getType)).eq?
    | throwError "lazy_eval: the goal is not an equation"
  let proof ← prove lhs rhs rules
  goal.assign proof
  replaceMainGoal []

end P4SpecTec.Tactic.LazyEval
