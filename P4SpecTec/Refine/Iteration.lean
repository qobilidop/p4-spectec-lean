import Batteries.Data.List.Basic
import P4SpecTec.Tactic.Audit
import P4SpecTec.Refine.Eval
import P4SpecTec.Refine.ValueShape

/-! Ordered list transport for AL iteration, retaining failures and fuel exhaustion. -/

namespace P4SpecTec.Refine

open P4SpecTec.Prelude P4SpecTec.Lang.Il

/-- Canonical list equality gives the element relation for an explicit encoding.
The encoding is explicit because AL pair carriers need not use the generic product instance. -/
theorem forall₂OfCanons {α : Type} (encode : α → value) {vs : List value} {xs : List α}
    (h : canons vs = canons (xs.map encode)) :
    List.Forall₂ (fun v x => canon v = canon (encode x)) vs xs := by
  induction xs generalizing vs with
  | nil =>
    have hv : vs = [] := canons_eq_nil h
    subst vs
    exact .nil
  | cons x xs ih =>
    obtain ⟨v, vs', rfl, hv, hvs⟩ := canons_eq_cons h
    exact .cons hv (ih hvs)

/-- info: 'P4SpecTec.Refine.forall₂OfCanons' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms forall₂OfCanons
#audit_axioms forall₂OfCanons

/-- Pointwise refinement transports an ordered monadic list traversal, preserving
both failure kinds for every defined reference result. Exhaustion imposes no result obligation. -/
theorem Refines.mapM {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop}
    {xs : List α} {ys : List β} {f : α → Eval γ} {g : β → Eval δ}
    (hinputs : List.Forall₂ P xs ys)
    (hstep : ∀ x y, P x y → Refines Q (f x) (g y)) :
    Refines (List.Forall₂ Q) (xs.mapM f) (ys.mapM g) := by
  induction hinputs with
  | nil =>
    simp only [List.mapM_nil]
    exact refines_pure .nil
  | @cons x y xs ys hxy hxs ih =>
    simp only [List.mapM_cons]
    apply refines_bind (hstep x y hxy)
    intro a b hab
    apply refines_bind ih
    intro as bs habs
    exact refines_pure (.cons hab habs)

/-- info: 'P4SpecTec.Refine.Refines.mapM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Refines.mapM
#audit_axioms Refines.mapM

end P4SpecTec.Refine
