import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.RCases
import P4SpecTec.Tactic.RunSound

/-!
The tactic `det` that discharges the generated determinism theorems
`R i o → R i o' → o = o'` of the `Prop` encoding (design section 10):
both derivations are destructured (`cases`), every pair of hypotheses
about the same relation on the same inputs is turned into an equation of
their outputs by that relation's own determinism theorem, and `simp_all`
propagates the equations the injectivity of `some` and `Except.ok`
gives (two hoisted calls on the same arguments have the same result).
The tactic is attempted only on relations with one rule path, no
recursion and no iterated premise (`Codegen/Props.lean`); a relation it
cannot close fails the build, which is what makes the theorem a check.
-/

namespace P4SpecTec.Tactic

open Lean Elab Tactic Meta

/-- The determinism theorem of the relation `r`, if it exists, with the
number of its inputs (the theorem's explicit binders before the outputs
are the inputs; its statement is `R ins outs → R ins outs' → …`). -/
def detFor (r : Name) : TacticM (Option (Name × Nat)) := do
  let thm := Name.str r "det"
  match (← getEnv).find? thm with
  | some info =>
    -- count the relation's arguments in the first hypothesis, minus the
    -- outputs: the inputs are those shared by both hypotheses
    let rec scan (t : Expr) : Option Nat :=
      match t with
      | .forallE _ d b _ =>
        let d := d.consumeMData
        if d.getAppFn.consumeMData.isConstOf r then
          match b with
          | .forallE _ d' _ _ =>
            let d' := d'.consumeMData
            let as := d.getAppArgs
            let bs := d'.getAppArgs
            -- the leading arguments the two hypotheses share are the inputs
            let shared := (as.zip bs).takeWhile (fun (x, y) => x == y)
            some shared.size
          | _ => none
        else scan b
      | _ => none
    pure ((scan info.type).map fun n => (thm, n))
  | none => pure none

/-- Every pair of hypotheses `R ins outs`, `R ins outs'` on the same inputs
yields `outs = outs'` by `R.det`; `true` when an equation was added. The
terms are built directly, since `cases` leaves the hypotheses
inaccessible. -/
def pairRelations : TacticM Bool := do
  if (← getGoals).isEmpty then return false
  let goal ← getMainGoal
  let (added, goal') ← goal.withContext do
    let mut hyps : Array (FVarId × Expr) := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if ty.getAppFn.consumeMData.isConst && !ty.isForall then
        let c := ty.getAppFn.consumeMData.constName!
        if (← getEnv).find? c matches some (.inductInfo _) then
          if ← isProp ty then hyps := hyps.push (decl.fvarId, ty)
    let mut g := goal
    let mut added := false
    for i in [0:hyps.size] do
      for j in [i+1:hyps.size] do
        let (h1, t1) := hyps[i]!
        let (h2, t2) := hyps[j]!
        let c := t1.getAppFn.consumeMData
        unless c == t2.getAppFn.consumeMData do continue
        let some (thm, n) ← detFor c.constName! | continue
        let as := t1.getAppArgs
        let bs := t2.getAppArgs
        if n > as.size || n > bs.size then continue
        unless (← (List.range n).allM fun k => isDefEq as[k]! bs[k]!) do continue
        -- already equal outputs: nothing to learn
        if ← (List.range (as.size - n)).allM fun k => isDefEq as[n + k]! bs[n + k]! then continue
        let pf ← try mkAppM thm #[.fvar h1, .fvar h2] catch _ => continue
        let ty ← inferType pf
        let (_, g') ← (← g.assert `det_h ty pf).intro1P
        g := g'
        added := true
    pure (added, g)
  replaceMainGoal [goal']
  pure added

/-- The injectivity simp set, then `subst_vars`. -/
def propagate : TacticM Unit := do
  let _ ← tryTac (evalTactic (← `(tactic| simp_all only [Option.some.injEq, Except.ok.injEq,
    Prod.mk.injEq, and_self, and_true, true_and, List.cons.injEq, reduceCtorEq])))
  if (← getGoals).isEmpty then return
  let _ ← tryTac (evalTactic (← `(tactic| subst_vars)))

/-- The tactic: see the module docstring. -/
elab "det" : tactic => do
  let _ ← introAll
  -- the two derivations are the last two hypotheses
  let names ← (← getMainGoal).withContext do
    let mut out : Array Name := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      if ← isProp (← instantiateMVars decl.type) then out := out.push decl.userName
    pure out
  for h in names.reverse.take 2 do
    evalTactic (← `(tactic| cases $(mkIdent h):ident))
  -- pair calls, equate their outputs, repeat: each equation can make
  -- the inputs of a later call agree
  propagate
  for _ in [0:64] do
    if (← getGoals).isEmpty then return
    unless ← pairRelations do break
    propagate
  if (← getGoals).isEmpty then return
  unless ← tryTac (evalTactic (← `(tactic| first | rfl | simp_all))) do
    throwError "det: cannot close{Lean.MessageData.ofGoal (← getMainGoal)}"
  unless (← getGoals).isEmpty do throwError "det: goals left open"

end P4SpecTec.Tactic
