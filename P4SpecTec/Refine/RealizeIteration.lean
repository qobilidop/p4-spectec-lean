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

/-- A reference step whose result the generated code has already computed purely: the
generated side takes no step, and the continuation receives the related reference result. -/
theorem Realizes.bindPure {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop}
    {m : Nat → Prelude.Eval α} {c : β} {next : Nat → α → Prelude.Eval γ}
    {n : Prelude.Eval δ} (hm : Realizes P m (Pure.pure c))
    (hn : ∀ a, P a c → Realizes Q (fun fuel => next fuel a) n) :
    Realizes Q (fun fuel => m fuel >>= next fuel) n := by
  intro q hq
  obtain ⟨r, hr, hrel⟩ := hm (.ok c) rfl
  cases r with
  | error _ => cases hrel
  | ok a =>
    obtain ⟨out, hout, hresult⟩ := hn a hrel q hq
    exact ⟨out, hr.bindOk hout, hresult⟩

/-- info: 'P4SpecTec.Refine.Realizes.bindPure' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Realizes.bindPure

/-- A reference traversal realizes the generated pure map of related inputs, element by
element; each element must realize its generated pure value. -/
theorem Realizes.mapMPureMap {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop}
    {f : Nat → α → Prelude.Eval γ} {g : β → δ} {xs : List α} {ys : List β}
    (hinputs : List.Forall₂ P xs ys)
    (hsteps : ∀ a b, P a b → Realizes Q (fun fuel => f fuel a) (Pure.pure (g b))) :
    Realizes (List.Forall₂ Q) (fun fuel => xs.mapM (f fuel)) (Pure.pure (ys.map g)) := by
  rw [← List.mapM_pure]
  exact Realizes.mapM hinputs hsteps

/-- info: 'P4SpecTec.Refine.Realizes.mapMPureMap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Realizes.mapMPureMap

end P4SpecTec.Refine
