import P4SpecTec.Interp.InterpAl.Interp

/-!
Operational interpreter equations that avoid inspecting irrelevant value payloads.
These are proved from the actual interpreter, including every raw value constructor.
-/

namespace P4SpecTec.Refine

open P4SpecTec.Interp_al P4SpecTec.Prelude

/-- Binding a source variable accepts every raw value without inspecting its payload. -/
theorem assignVar (fuel : Nat) (ctx : Ctx.t) (i : Lang.Il.id) (t : Lang.Il.typ')
    (region : Util.Source.region) (v : Lang.Il.value) :
    Interp.assign_exp (fuel + 1) ctx ⟨.VarE i, t, region⟩ v =
      pure (Ctx.add_value ctx (i, []) v) := by
  cases v with
  | mk it note region => cases it <;> rfl

/-- info: 'P4SpecTec.Refine.assignVar' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignVar

end P4SpecTec.Refine
