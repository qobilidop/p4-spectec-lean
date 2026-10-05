import Init.Internal.Order.Basic

/-!
Realization of approximants in a least fixed point (not a mirror). A recursive group of
generated definitions is `Lean.Order.fix F hmono` in the flat order on `Option`. Induction
over that fixed point reasons about approximants below it, while the structural rules of a
logical relation are stated over the final functions. Monotonicity of `F`, which Lean
proved when it accepted the definitions, keeps one unfolding over approximants below the
fixed point, and in the flat order a defined outcome below another is that outcome: no
symbolic proof per definition.
-/

namespace P4SpecTec.Refine

open Lean.Order

/-- In the flat order a defined outcome below another outcome is that outcome. -/
theorem flatSome {α : Type u} {a b : Option α} {r : α} (h : a ⊑ b) (ha : a = some r) :
    b = some r := by
  cases h with
  | bot => cases ha
  | refl => exact ha

/-- info: 'P4SpecTec.Refine.flatSome' does not depend on any axioms -/
#guard_msgs in #print axioms flatSome

/-- One unfolding of a monotone functional over an approximant below its least fixed point
stays below the fixed point. -/
theorem fixStepLe {α : Sort u} [CCPO α] {f : α → α} (hf : monotone f) {x : α}
    (h : x ⊑ fix f hf) : f x ⊑ fix f hf := by
  rw [fix_eq hf]
  exact hf x _ h

/-- info: 'P4SpecTec.Refine.fixStepLe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fixStepLe

/-- Being below a fixed element is preserved by suprema of chains. -/
theorem admissibleLe {α : Sort u} [CCPO α] (y : α) : admissible (fun x : α => x ⊑ y) :=
  fun _ hc h => csup_le hc h

/-- info: 'P4SpecTec.Refine.admissibleLe' depends on axioms: [Classical.choice] -/
#guard_msgs in #print axioms admissibleLe

/-- The first components of ordered tuples are ordered. -/
theorem pprodLeFst {α : Sort u} {β : Sort v} [CCPO α] [CCPO β] {a b : α ×' β} (h : a ⊑ b) :
    a.1 ⊑ b.1 := h.1

/-- info: 'P4SpecTec.Refine.pprodLeFst' does not depend on any axioms -/
#guard_msgs in #print axioms pprodLeFst

/-- The second components of ordered tuples are ordered. -/
theorem pprodLeSnd {α : Sort u} {β : Sort v} [CCPO α] [CCPO β] {a b : α ×' β} (h : a ⊑ b) :
    a.2 ⊑ b.2 := h.2

/-- info: 'P4SpecTec.Refine.pprodLeSnd' does not depend on any axioms -/
#guard_msgs in #print axioms pprodLeSnd

/-- A hypothesis kept from simplification. A step that simplifies with every hypothesis
would use an induction hypothesis `∀ args, run = some _ → R args` as a rewrite rule and
erase each fact `R args` obtained from it. -/
structure Kept (p : Prop) : Prop where
  /-- The kept statement. -/
  out : p

end P4SpecTec.Refine
