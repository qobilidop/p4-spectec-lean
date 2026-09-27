import P4SpecTec.Refine.Realize
import P4SpecTec.Refine.Call

/-! Ordered paired-input transport for reverse iteration, with exact list truncation. -/

namespace P4SpecTec.Refine

/-- Zipping related lists preserves both positional relations, including unequal lengths
between the two input columns. Each source column is related to its own generated column. -/
theorem forall₂Zip {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop}
    {as : List α} {bs : List β} {cs : List γ} {ds : List δ}
    (hab : List.Forall₂ P as bs) (hcd : List.Forall₂ Q cs ds) :
    List.Forall₂ (fun a b => P a.1 b.1 ∧ Q a.2 b.2) (as.zip cs) (bs.zip ds) := by
  induction hab generalizing cs ds with
  | nil => exact .nil
  | cons h _ ih =>
    cases hcd with
    | nil => exact .nil
    | cons hcd htail => exact .cons ⟨h, hcd⟩ (ih htail)

/-- info: 'P4SpecTec.Refine.forall₂Zip' does not depend on any axioms -/
#guard_msgs in #print axioms forall₂Zip

/-- An iteration that binds no output variables yields an empty transposed batch.
The positional relation certifies every actual row, including any metadata it could carry. -/
theorem transposeRelatedEmpty {β : Type} {rows : List (List Lang.Il.value)} {ys : List β}
    (h : List.Forall₂ (fun row _ => row = []) rows ys) :
    Interp_al.Ctx.transpose rows = (pure [] : Prelude.Eval (List (List Lang.Il.value))) := by
  apply transposeEmptyRows
  induction h with
  | nil => simp
  | @cons row y rows ys head tail ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact head
    · exact ih r hr

/-- info: 'P4SpecTec.Refine.transposeRelatedEmpty' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transposeRelatedEmpty

/-- Already executed output-free iterations may precede the related remaining batch. -/
theorem transposeRelatedEmptyPrefix {β : Type} {rows : List (List Lang.Il.value)}
    {ys : List β} (count : Nat) (h : List.Forall₂ (fun row _ => row = []) rows ys) :
    Interp_al.Ctx.transpose (List.replicate count [] ++ rows) =
      (pure [] : Prelude.Eval (List (List Lang.Il.value))) := by
  have hrows : ∀ row ∈ rows, row = [] := by
    induction h with
    | nil => simp
    | @cons row y rows ys head tail ih =>
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact head
      · exact ih r hr
  apply transposeEmptyRows
  intro row hrow
  rcases List.mem_append.mp hrow with hprefix | htail
  · exact (List.mem_replicate.mp hprefix).2
  · exact hrows row htail

/-- info: 'P4SpecTec.Refine.transposeRelatedEmptyPrefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transposeRelatedEmptyPrefix

end P4SpecTec.Refine
