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

/-- An output-free source iteration uses the same traversal in its empty case.
The actual context construction, premise evaluation and transpose failures are preserved. -/
theorem iterPremListNoOutputs (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (premise : Lang.Il.prem) (variables : List Lang.Il.var) :
    Interp.eval_iter_prem_list (fuel + 1) cfg ctx premise variables [] = (do
      let contexts ← Ctx.sub_list ctx variables
      let rows ← contexts.mapM fun sub => do
        let _ ← Interp.eval_prem fuel cfg sub premise
        pure ([] : List Lang.Il.value)
      let _ ← Ctx.transpose rows
      pure ctx) := by
  simp only [Interp.eval_iter_prem_list]
  congr 1
  funext contexts
  cases contexts <;>
    simp only [List.map_nil, List.zip_nil_left, List.foldl_nil, Ctx.find_values,
      List.mapM_nil, pure_bind, Ctx.transpose] <;> rfl

/-- info: 'P4SpecTec.Refine.iterPremListNoOutputs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms iterPremListNoOutputs

end P4SpecTec.Refine
