import P4SpecTec.Refine.IterationColumns
import P4SpecTec.Interp.InterpAl.Interp

/-! Exact operational equations for source list premises with declared output columns. -/

namespace P4SpecTec.Refine

open P4SpecTec.Interp_al P4SpecTec.Prelude P4SpecTec.Lang.Il

/-- Expose the actual row traversal before collecting its declared output columns.
The empty batch still binds every declared output to an empty list. Context lookup,
ordered premise execution, transpose checks, metadata and both failures are unchanged. -/
theorem iterPremListColumns (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (premise : prem) (bound bind : List var) :
    Interp.eval_iter_prem_list (fuel + 1) cfg ctx premise bound bind = (do
      let contexts ← Ctx.sub_list ctx bound
      let rows ← contexts.mapM fun sub => do
        let sub ← Interp.eval_prem fuel cfg sub premise
        Ctx.find_values sub (bind.map fun v => (v.id, v.iters))
      let columns ← collectColumns bind.length rows
      pure ((bind.zip columns).foldl (fun ctx (v, values) =>
        let typ := Runtime.Type.Typ.Make.iterate v.typ (v.iters ++ [.List])
        Ctx.add_value ctx (v.id, v.iters ++ [.List])
          (Runtime.Value.Make.list typ.it values)) ctx)) := by
  simp only [Interp.eval_iter_prem_list]
  congr 1
  funext contexts
  cases contexts <;>
    simp only [List.mapM_nil, List.mapM_cons, pure_bind, bind_assoc, collectColumns,
      List.map_const'] <;> rfl

/-- info: 'P4SpecTec.Refine.iterPremListColumns' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms iterPremListColumns
#audit_axioms iterPremListColumns

end P4SpecTec.Refine
