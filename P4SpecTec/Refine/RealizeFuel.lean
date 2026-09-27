import P4SpecTec.Refine.Realize

/-!
Fuel-family transport for reverse symbolic execution. Each proof supplies its own
eventual bound; these rules assume no fuel monotonicity of the interpreter.
-/

namespace P4SpecTec.Refine

open P4SpecTec.Prelude

/-- Discarding a fixed initial fuel segment preserves an eventual witness. -/
theorem EventuallyRuns.add (h : EventuallyRuns m r) (offset : Nat) :
    EventuallyRuns (fun fuel => m (fuel + offset)) r := by
  obtain ⟨bound, hbound⟩ := h
  exact ⟨bound, fun fuel hfuel => hbound (fuel + offset) (by omega)⟩

/-- info: 'P4SpecTec.Refine.EventuallyRuns.add' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms EventuallyRuns.add

/-- A witness above a fixed offset supplies a witness for the original family. -/
theorem EventuallyRuns.ofAdd (offset : Nat)
    (h : EventuallyRuns (fun fuel => m (fuel + offset)) r) : EventuallyRuns m r := by
  obtain ⟨bound, hbound⟩ := h
  refine ⟨bound + offset, fun fuel hfuel => ?_⟩
  have hrun := hbound (fuel - offset) (by omega)
  simpa only [Nat.sub_add_cancel (show offset ≤ fuel by omega)] using hrun

/-- info: 'P4SpecTec.Refine.EventuallyRuns.ofAdd' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms EventuallyRuns.ofAdd

/-- Reverse correspondence is unchanged when a fixed fuel prefix is discarded. -/
theorem Realizes.add (h : Realizes P reference generated) (offset : Nat) :
    Realizes P (fun fuel => reference (fuel + offset)) generated := by
  intro q hq
  obtain ⟨r, hr, hp⟩ := h q hq
  exact ⟨r, hr.add offset, hp⟩

/-- info: 'P4SpecTec.Refine.Realizes.add' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Realizes.add

/-- Account for a fixed number of reference helper entries before symbolic execution. -/
theorem Realizes.ofAdd (offset : Nat)
    (h : Realizes P (fun fuel => reference (fuel + offset)) generated) :
    Realizes P reference generated := by
  intro q hq
  obtain ⟨r, hr, hp⟩ := h q hq
  exact ⟨r, hr.ofAdd offset, hp⟩

/-- info: 'P4SpecTec.Refine.Realizes.ofAdd' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Realizes.ofAdd

/-- A local generated let-binding can be named without changing its computation. -/
theorem Realizes.have {P : α → β → Prop} {reference : Nat → Eval α}
    {a : γ} {next : γ → Eval β}
    (h : ∀ x, x = a → Realizes P reference (next x)) :
    Realizes P reference (have x := a; next x) := h a rfl

/-- info: 'P4SpecTec.Refine.Realizes.have' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Realizes.have

/-- Specialize compositional reverse correspondence to a known generated outcome. -/
theorem Realizes.outcome {P : α → β → Prop} {reference : Nat → Eval α}
    {generated : Eval β} (h : Realizes P reference generated)
    (hq : generated.run = some q) :
    ∃ r, EventuallyRuns reference r ∧ ResRel P r q := h q hq

/-- info: 'P4SpecTec.Refine.Realizes.outcome' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Realizes.outcome

end P4SpecTec.Refine
