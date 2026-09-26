import Lean.Elab.Tactic.Monotonicity
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.Assumption

/-!
Checked monotonicity for generated callback consumers. The fallback exposes
only explicitly named generated definitions and their fixed-point helpers.
It does not assign a monotonicity contract to arbitrary externs or callbacks.
-/

namespace P4SpecTec.Tactic

open Lean Meta Elab Tactic Lean.Order

/-- Least fixed points vary monotonically with a monotone external parameter. -/
@[partial_fixpoint_monotone]
theorem monotoneFix {γ α : Type} [PartialOrder γ] [CCPO α]
    (F : γ → α → α) (hf : ∀ x, monotone (F x)) (hF : monotone F) :
    monotone (fun x => fix (F x) (hf x)) := by
  intro x y hxy
  apply fix_induct (hf x) (fun a => a ⊑ fix (F y) (hf y))
  · intro c hc h
    exact csup_le hc h
  · intro a ha
    apply PartialOrder.rel_trans (hF x y hxy a)
    have h := hf y a (fix (F y) (hf y)) ha
    rw [← fix_eq (hf y)] at h
    exact h

/-- info: 'P4SpecTec.Tactic.monotoneFix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms monotoneFix

/-- Pointwise chain suprema preserve monotonicity in a callback argument. -/
theorem admissibleMonotone {γ α : Type} [PartialOrder γ] [CCPO α] :
    admissible (fun f : γ → α => monotone f) := by
  intro c hc h x y hxy
  rw [← fun_csup_eq c hc]
  apply csup_le (chain_apply hc x)
  intro a ⟨f, hf, ha⟩
  subst a
  exact PartialOrder.rel_trans (h f hf x y hxy)
    (le_csup (chain_apply hc y) ⟨f, hf, rfl⟩)

/-- info: 'P4SpecTec.Tactic.admissibleMonotone' depends on axioms:
[Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms admissibleMonotone

/-- A callback-monotone body has a callback-monotone least fixed point. -/
@[partial_fixpoint_monotone]
theorem monotoneFixArgument {δ γ α : Type} [PartialOrder δ] [PartialOrder γ] [CCPO α]
    (F : (γ → α) → γ → α) (hf : monotone F)
    (hF : ∀ f, monotone f → monotone (F f)) (g : δ → γ) (hg : monotone g) :
    monotone (fun x => fix F hf (g x)) := by
  have hm : monotone (fix F hf) := fix_induct hf _ admissibleMonotone hF
  exact fun x y hxy => hm _ _ (hg x y hxy)

/-- info: 'P4SpecTec.Tactic.monotoneFixArgument' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms monotoneFixArgument

/-- Solve compositionally, exposing listed consumers only when needed.
Every successful path builds an ordinary kernel-checked proof term. -/
partial def solveGeneratedMonotonicity (names : Array Name) (goal : MVarId) : MetaM Unit :=
    withIncRecDepth <| goal.withContext do
  checkSystem "codegen monotonicity"
  try
    goal.assumption
    return
  catch _ => pure ()
  let saved ← saveState
  try
    let goals ← Monotonicity.solveMonoStep (goal := goal)
    for g in goals do solveGeneratedMonotonicity names g
  catch original =>
    saved.restore
    let target ← instantiateMVars (← goal.getType)
    let_expr monotone _ _ _ _ f := target | throw original
    let f ← if f.isLambda then pure f else etaExpand f
    let f := Monotonicity.headBetaUnderLambda f
    let body := f.bindingBody!
    for localDecl in (← goal.getDecl).lctx do
      if localDecl.isImplementationDetail then continue
      try
        let h := localDecl.toExpr
        let_expr monotone _ _ _ _ consumer := (← inferType h) | continue
        if !body.isApp || body.appFn! != consumer then continue
        let arg := f.updateLambda! f.bindingInfo! f.bindingDomain! body.appArg!
        let hg ← mkFreshExprMVar (← mkAppM ``monotone #[arg])
        goal.assign (← mkAppM ``monotone_compose #[hg, h])
        solveGeneratedMonotonicity names hg.mvarId!
        return
      catch _ => saved.restore
    try
      unless body.isApp && !body.appArg!.hasLooseBVars do throw original
      let goals ← goal.applyConst ``Lean.Order.monotone_apply
      for g in goals do solveGeneratedMonotonicity names g
    catch _ =>
      saved.restore
      let target ← goal.getType
      let expanded ← deltaExpand target fun n =>
        names.contains n || names.any (fun base => n == Name.str base "mutual")
      if expanded == target then throw original
      let next ← goal.replaceTargetDefEq expanded
      solveGeneratedMonotonicity names next

/-- A monotonicity proof may expose these generated callback consumers. -/
syntax (name := codegenMonotonicity) "codegen_monotonicity" "[" ident,* "]" : tactic

/-- Elaborate the explicit consumer list and discharge the monotonicity goal. -/
@[tactic codegenMonotonicity]
def evalCodegenMonotonicity : Tactic := fun stx => withoutRecover do
  let names ← stx[2].getSepArgs.mapM fun id => do
    realizeGlobalConstNoOverloadWithInfo id
  liftMetaFinishingTactic (solveGeneratedMonotonicity names)

end P4SpecTec.Tactic
