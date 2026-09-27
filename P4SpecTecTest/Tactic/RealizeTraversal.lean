import P4SpecTec.Tactic.RealizeTraversal
import P4SpecTec.Tactic.Audit

/-! Zipped reverse-traversal inputs preserve explicit canonical observations. -/

namespace P4SpecTecTest.Tactic.RealizeTraversal

open Lean Elab Tactic Meta P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine

elab "prove_zipped_inputs" : tactic => withoutRecover do
  let goal ← getMainGoal
  let ty ← withMainContext do instantiateMVars (← goal.getType)
  let rules ← P4SpecTec.Tactic.simpSet
  let some proof ← P4SpecTec.Tactic.traversalInputs (P4SpecTec.Tactic.proveValue rules)
      (ty.getArg! 3) (ty.getArg! 4)
    | throwError "no positional input proof"
  goal.assign proof
  replaceMainGoal []

theorem observedZip (raw : List Lang.Il.value) (typed : List Nat)
    (v : Lang.Il.value) (n : Nat)
    (hlist : canons raw = canons (typed.map toValue)) (hvalue : Rel v n) :
    List.Forall₂ (fun a b => Rel a.1 b.1 ∧ Rel a.2 b.2)
      (raw.zip [v]) (typed.zip [n]) := by
  prove_zipped_inputs

/-- info: 'P4SpecTecTest.Tactic.RealizeTraversal.observedZip' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observedZip
#audit_axioms observedZip

theorem emptyPrefix (rows : List (List Lang.Il.value)) (ys : List Unit)
    (h : List.Forall₂ (fun row _ => row = []) rows ys) :
    Interp_al.Ctx.transpose ([] :: [] :: rows) =
      (pure [] : Eval (List (List Lang.Il.value))) := by
  run_tac
    let ty ← withMainContext do instantiateMVars (← (← getMainGoal).getType)
    unless ← P4SpecTec.Tactic.emptyTraversalResult (ty.getArg! 1) do
      throwError "empty output prefix was not transported"

/-- info: 'P4SpecTecTest.Tactic.RealizeTraversal.emptyPrefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms emptyPrefix
#audit_axioms emptyPrefix

theorem unencodedInputs (raw typed : List Lang.Il.value)
    (_h : canons raw = canons typed) : True := by
  run_tac
    let before ← getGoals
    withMainContext do
      let some raw := (← getLCtx).findFromUserName? `raw | throwError "missing raw binder"
      let some typed := (← getLCtx).findFromUserName? `typed | throwError "missing typed binder"
      let result ← P4SpecTec.Tactic.traversalInputs
        (throwError "unexpected literal proof") raw.toExpr typed.toExpr
      unless result.isNone && (← getGoals) == before do
        throwError "unencoded inputs changed the proof goal"
  exact True.intro

/-- info: 'P4SpecTecTest.Tactic.RealizeTraversal.unencodedInputs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unencodedInputs
#audit_axioms unencodedInputs

end P4SpecTecTest.Tactic.RealizeTraversal
