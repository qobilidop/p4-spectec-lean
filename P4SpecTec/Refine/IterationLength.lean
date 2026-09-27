import P4SpecTec.Refine.Iteration
import P4SpecTec.Refine.Realize

/-! Ordered traversal transport with the exact successful output length retained. -/

namespace P4SpecTec.Refine
open P4SpecTec.Prelude

/-- Transport an ordered traversal and retain its generated input/output length equality.
Failure outcomes remain unchanged; the length fact describes only successful traversals. -/
theorem Refines.mapMWithLength {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop}
    {xs : List α} {ys : List β} {f : α → Eval γ} {g : β → Eval δ}
    (hinputs : List.Forall₂ P xs ys)
    (hstep : ∀ x y, P x y → Refines Q (f x) (g y)) :
    Refines (fun outputs results => List.Forall₂ Q outputs results ∧ results.length = ys.length)
      (xs.mapM f) (ys.mapM g) := by
  induction hinputs with
  | nil =>
    simp only [List.mapM_nil]
    exact refines_pure ⟨.nil, rfl⟩
  | @cons x y xs ys hxy hxs ih =>
    simp only [List.mapM_cons]
    apply refines_bind (hstep x y hxy)
    intro a b hab
    apply refines_bind ih
    intro as bs habs
    exact refines_pure ⟨.cons hab habs.1, by simp only [List.length_cons, habs.2]⟩

/-- info: 'P4SpecTec.Refine.Refines.mapMWithLength' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Refines.mapMWithLength
#audit_axioms Refines.mapMWithLength

/-- Transport an ordered traversal and retain its generated input/output length equality.
Failure outcomes remain unchanged; the length fact describes only successful traversals. -/
theorem Realizes.mapMWithLength {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop}
    {f : Nat → α → Eval γ} {g : β → Eval δ} {xs : List α} {ys : List β}
    (hinputs : List.Forall₂ P xs ys)
    (hsteps : ∀ a b, P a b → Realizes Q (fun fuel => f fuel a) (g b)) :
    Realizes (fun outputs results => List.Forall₂ Q outputs results ∧ results.length = ys.length)
      (fun fuel => xs.mapM (f fuel)) (ys.mapM g) := by
  induction hinputs with
  | nil =>
    simp only [List.mapM_nil]
    exact Realizes.pure ⟨.nil, rfl⟩
  | @cons a b xs ys hab _ ih =>
    simp only [List.mapM_cons]
    apply Realizes.bind (hsteps a b hab)
    intro c d hcd
    apply Realizes.bind ih
    intro cs ds htail
    exact Realizes.pure ⟨.cons hcd htail.1, by simp only [List.length_cons, htail.2]⟩

/-- info: 'P4SpecTec.Refine.Realizes.mapMWithLength' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Realizes.mapMWithLength
#audit_axioms Realizes.mapMWithLength
end P4SpecTec.Refine
