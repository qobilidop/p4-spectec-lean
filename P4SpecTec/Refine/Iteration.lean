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

/-- Pointwise canonical relations give canonical list equality under an explicit encoding.
This is the converse of `forall₂OfCanons`, used after an iterated expression's traversal. -/
theorem canonsOfForall₂ {α : Type} (encode : α → value) {vs : List value} {xs : List α}
    (h : List.Forall₂ (fun v x => canon v = canon (encode x)) vs xs) :
    canons vs = canons (xs.map encode) := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp only [canons, List.map_cons, head, ih]

/-- info: 'P4SpecTec.Refine.canonsOfForall₂' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonsOfForall₂
#audit_axioms canonsOfForall₂

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

/-- An interpreter step against a value the generated code has already computed purely.
The generated side takes no step; the continuation receives the related result. -/
theorem refines_bind_pure {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop}
    {m : Eval α} {c : β} {k : α → Eval γ} {n : Eval δ}
    (h₁ : Refines P m (pure c)) (h₂ : ∀ a, P a c → Refines Q (k a) n) :
    Refines Q (m >>= k) n := by
  intro r hr
  rw [run_bind] at hr
  cases hm : m.run with
  | none => rw [hm] at hr; cases hr
  | some s =>
    rw [hm] at hr
    obtain ⟨s', hn, hres⟩ := h₁ s hm
    have hs : s' = .ok c := (Option.some.inj hn).symm
    subst hs
    cases s with
    | error _ => exact absurd hres id
    | ok a =>
      simp only [ResRel] at hres
      simp only [Option.bind_some] at hr
      exact h₂ a hres r hr

/-- info: 'P4SpecTec.Refine.refines_bind_pure' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms refines_bind_pure
#audit_axioms refines_bind_pure

/-- An ordered reference traversal against the generated pure map of related inputs,
element by element; a failing or diverging reference element imposes its usual obligation. -/
theorem refines_mapM_pureMap {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop}
    {xs : List α} {ys : List β} {f : α → Eval γ} {g : β → δ}
    (hinputs : List.Forall₂ P xs ys)
    (hstep : ∀ x y, P x y → Refines Q (f x) (pure (g y))) :
    Refines (List.Forall₂ Q) (xs.mapM f) (pure (ys.map g)) := by
  rw [← List.mapM_pure]
  exact Refines.mapM hinputs hstep

/-- info: 'P4SpecTec.Refine.refines_mapM_pureMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms refines_mapM_pureMap
#audit_axioms refines_mapM_pureMap

end P4SpecTec.Refine
