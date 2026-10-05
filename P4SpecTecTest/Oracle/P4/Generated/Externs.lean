import P4SpecTec.BackendSim.Placeholder
import P4Spec

/-!
Not a mirror. The placeholder target as the generated full-P4 library's `Externs`
instance, shared by the generated replay legs. The compile-time extern call runs the same
ported `Placeholder.eval_extern_func_lctk_call` as the reference interpreter's leg: its
arguments are encoded as IL values, its one callback (`find_var_value_t`) decodes them,
calls the generated function and encodes the result, and the outcome is decoded again.
A value outside the expected generated type is a hard error, never a repaired value.
-/

namespace P4SpecTecTest.Diff.P4Generated

open P4SpecTec P4SpecTec.Prelude P4SpecTec.BackendSim

/-- Fuel for the value decoders, a nesting bound far above any replayed case's depth. -/
def decodeFuel : Nat := 100000000

/-- Decode at the generated type, or fail hard. -/
def decoded {α : Type} [OfValue α] (v : Lang.Il.value) : StateEval α :=
  match OfValue.ofValue decodeFuel v with
  | some x => pure x
  | none => throw .err

/-- The spec functions the placeholder calls back, on the generated library, registered as
upstream registers its trampoline: a failure of the generated function is a mismatch
(`Make.call_func`). Decoding its arguments is this adapter's, so a failure there, or an
unknown callback, stays a hard error. -/
def call : Placeholder.Call StateEval := fun name typs values =>
  match name, values with
  | "find_var_value_t", [value_name, value_cursor, value_ctx] => do
    let name_ ← decoded value_name
    let cursor ← decoded value_cursor
    let ctx ← decoded value_ctx
    Make.call_func (fun _ _ _ => do
      pure (toValue (← ExceptT.mk (P4Spec.«$find_var_value_t» name_ cursor ctx))))
      name typs values
  | _, _ => throw .err

/-- The pinned placeholder externs: null state initializers, `static_assert` at compile
time, and a hard error for every runtime extern call. -/
instance placeholderExterns : P4Spec.Externs where
  ExternFunctionCall_eval_lctk := fun ctx name parameters => StateEval.run do
    let [value] ← Placeholder.eval_extern_rel call
      "ExternFunctionCall_eval_lctk" [toValue ctx, toValue name, toValue parameters]
      | throw .err
    decoded value
  «$init_objectState» := fun _ _ _ _ => StateEval.run (pure ExternValue.null)
  «$init_archState» := StateEval.run (pure ExternValue.null)
  ExternFunctionCall_eval := fun _ _ _ _ => StateEval.run (throw .err)
  ExternMethodCall_eval := fun _ _ _ _ _ => StateEval.run (throw .err)

end P4SpecTecTest.Diff.P4Generated
