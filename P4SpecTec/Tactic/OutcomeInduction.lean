import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm

/-! Shared application of generated mutual outcome-induction principles. -/

namespace P4SpecTec.Tactic

open Lean Elab Tactic Meta

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

/-- Apply joint outcome induction in Lean's declaration order, then reassemble
conjuncts in the requested order. Each case must be closed by `dischargeCase`. -/
def proveOutcomeGroup (principle : Name) (dischargeCase : TacticM Unit) : TacticM Unit := do
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
        throwError "outcome induction: no conjunct for {f}; the principle's conjuncts are:{listed}"
    let ordered ← leanOrder.mapM partOf
    let permuted := ordered.dropLast.foldr (fun a acc => mkApp2 (mkConst ``And) a acc)
      ordered.getLast!
    let hm ← mkFreshExprMVar permuted
    setGoals [hm.mvarId!]
    evalTactic (← `(tactic| apply $(mkIdent principle):ident))
    let cases ← getGoals
    for g in cases do
      setGoals [g]
      dischargeCase
      unless (← getGoals).isEmpty do throwError "outcome induction: case left open"
    setGoals []
    unless (← getGoals).isEmpty do throwError "outcome induction: cases left open"
    -- reassemble: the k-th conjunct of the goal is a projection of `hm`
    let proj (k : Nat) : MetaM Expr := do
      let mut e := hm
      let n := ordered.length
      for _ in List.range k do e ← mkAppM ``And.right #[e]
      if k < n - 1 then mkAppM ``And.left #[e] else pure e
    let mut proofs : List Expr := []
    for e in parts do
      let f := conjunctFunction e
      let some k := leanOrder.idxOf? f | throwError "outcome induction: no case for {f}"
      proofs := proofs ++ [← proj k]
    let mut proof := proofs.getLast!
    for a in proofs.dropLast.reverse do
      proof ← mkAppM ``And.intro #[a, proof]
    proof ← instantiateMVars proof
    let ok ← isDefEq (← inferType proof) target
    unless ok do throwError "outcome induction: reassembled statement does not match"
    goal.assign proof
    setGoals []

end P4SpecTec.Tactic
