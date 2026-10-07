import P4SpecTec.Runtime.Value.Value
import P4SpecTec.Prelude.StateEval
import P4SpecTec.BackendSim.SpecImpl.Pack

/-!
Port of `p4spec/lib/backend-sim/spec_impl/func.ml`: the helpers that call functions of
the spec through the trampoline registered at initialization, here an explicit `Call` in
the caller's effect carrier. Each helper builds upstream's argument values as it does, and
an `Option.get` or getter upstream raises on is the hard error `Fail.err`. This is the
pinned full-P4 prefixed-name/cursor ABI, not Nano's distinct scope/context/name ABI.
-/

namespace P4SpecTec.BackendSim.SpecImpl.Func

open P4SpecTec.Lang.Il P4SpecTec.Lang.Xl P4SpecTec.Runtime P4SpecTec.Prelude
open P4SpecTec.Util.Source

/-- Explicit counterpart of the mutable Spec.Func.call trampoline. -/
abbrev Call (m : Type → Type) := String → List typ → List value → m value

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- Require a runtime value shape, matching upstream's raising getters. -/
def required {α : Type} (result : Option α) : m α :=
  match result with | some x => pure x | none => throw .err

/-- The number of an output, as `Value.Get.num` followed by `Num.to_int`. -/
def integer (v : value) : m Int := do pure (Num.to_int (← required (Value.Get.num v)))

/-- Mirrors `write_value_from_bits`. -/
def write_value_from_bits (call : Call m) (value_target : value) (varsize : Nat)
    (bits : Array Bool) : m value :=
  let typ_bits : typ' := .IterT (mkPhrase (.VarT (mkPhrase "bit") [])) .List
  let value_bits := Value.Make.list typ_bits (bits.toList.map Value.Make.bool)
  call "write_value_from_bits" [] [value_target, Value.Make.nat varsize, value_bits]

/-- Mirrors `write_bits_from_value`. -/
def write_bits_from_value (call : Call m) (value_source : value) : m value :=
  call "write_bits_from_value" [] [value_source]

/-- Mirrors `bitacc_range_op`. -/
def bitacc_range_op (call : Call m) (value_base value_hi value_lo : value) : m value :=
  call "bitacc_range_op" [] [value_base, value_hi, value_lo]

/-- Mirrors `default`. -/
def default (call : Call m) (value_typ : value) : m value := call "default" [] [value_typ]

/-- Mirrors `cast_op`. -/
def cast_op (call : Call m) (value_typ value_value : value) : m value :=
  call "cast_op" [] [value_typ, value_value]

/-- Mirrors `sizeof_minSizeInBits'`. -/
def sizeof_minSizeInBits' (call : Call m) (value_typ : value) : m Int := do
  integer (← call "sizeof_minSizeInBits'" [] [value_typ])

/-- Mirrors `sizeof_maxSizeInBits'`. -/
def sizeof_maxSizeInBits' (call : Call m) (value_typ : value) : m Int := do
  integer (← call "sizeof_maxSizeInBits'" [] [value_typ])

/-- Mirrors `key_interface_of_tableObject`: the table's key names, match kinds and types. -/
def key_interface_of_tableObject (call : Call m) (value_tableObject : value) :
    m (List (value × value × value)) := do
  let entries ← required (Value.Get.list (← call "key_interface_of_tableObject" []
    [value_tableObject]))
  entries.mapM fun entry => do
    match ← required (Value.Get.tuple entry) with
    | [a, b, c] => pure (a, b, c)
    | _ => throw .err

/-- Mirrors `tableObject_add_entry`. -/
def tableObject_add_entry (call : Call m) (value_ctx value_tableObject
    value_tableEntryPriorityInterface value_tableKeysetInterface
    value_tableActionInterface : value) : m (Option value) := do
  required (Value.Get.opt (← call "tableObject_add_entry" []
    [value_ctx, value_tableObject, value_tableEntryPriorityInterface,
      value_tableKeysetInterface, value_tableActionInterface]))

/-- Mirrors `tableObject_add_default_action`. -/
def tableObject_add_default_action (call : Call m)
    (value_ctx value_tableObject value_tableActionInterface : value) : m value :=
  call "tableObject_add_default_action" []
    [value_ctx, value_tableObject, value_tableActionInterface]

/-- Mirrors `find_object_qualified_e`. -/
def find_object_qualified_e (call : Call m) (value_arch value_objectId : value) :
    m (Option value) := do
  required (Value.Get.opt (← call "find_object_qualified_e" [] [value_arch, value_objectId]))

/-- Mirrors `find_object_unqualified_e`. -/
def find_object_unqualified_e (call : Call m) (value_arch value_id : value) :
    m (Option value) := do
  required (Value.Get.opt (← call "find_object_unqualified_e" [] [value_arch, value_id]))

/-- Mirrors `update_object_qualified_e`. -/
def update_object_qualified_e (call : Call m) (value_arch value_objectId value_object : value) :
    m value :=
  call "update_object_qualified_e" [] [value_arch, value_objectId, value_object]

/-- Mirrors `update_object_unqualified_e`. -/
def update_object_unqualified_e (call : Call m) (value_arch value_id value_object : value) :
    m value :=
  call "update_object_unqualified_e" [] [value_arch, value_id, value_object]

/-- Mirrors `find_objectState_e`, including its `Option.get`. -/
def find_objectState_e (call : Call m) (value_arch value_objectId : value) : m value := do
  required (← required (Value.Get.opt
    (← call "find_objectState_e" [] [value_arch, value_objectId])))

/-- Mirrors `update_objectState_e`, including its `Option.get`. -/
def update_objectState_e (call : Call m) (value_arch value_objectId value_objectState : value) :
    m value := do
  required (← required (Value.Get.opt (← call "update_objectState_e" []
    [value_arch, value_objectId, value_objectState])))

/-- Mirrors `find_archState_e`. -/
def find_archState_e (call : Call m) (value_arch : value) : m value :=
  call "find_archState_e" [] [value_arch]

/-- Mirrors `update_archState_e`. -/
def update_archState_e (call : Call m) (value_arch value_archState : value) : m value :=
  call "update_archState_e" [] [value_arch, value_archState]

/-- Mirrors `find_type_e`. -/
def find_type_e (call : Call m) (value_cursor value_ctx : value) (name : ByteText) : m value :=
  call "find_type_e" [] [value_cursor, value_ctx, Value.Make.text name]

/-- Mirrors `find_type_e_local`, including its `Option.get`. -/
def find_type_e_local (call : Call m) (value_ctx : value) (name : ByteText) : m value := do
  required (← required (Value.Get.opt (← find_type_e call Pack.cursorLocal value_ctx name)))

/-- Mirrors find_var_value_t, the typing-context lookup, with the same name construction
and argument order as find_var_e. -/
def find_var_value_t (call : Call m) (value_cursor value_ctx : value) (name : String) :
    m value :=
  call "find_var_value_t" [] [Pack.bareName (ByteText.ofString name), value_cursor, value_ctx]

/-- Mirrors find_var_value_t_local, with the pinned cursor type note. -/
def find_var_value_t_local (call : Call m) (value_ctx : value) (name : String) : m value :=
  find_var_value_t call Pack.cursorLocal value_ctx name

/-- Mirrors find_var_e, including prefixed name construction and argument order. -/
def find_var_e (call : Call m) (value_cursor value_ctx : value) (name : String) :
    m value :=
  call "find_var_e" [] [Pack.bareName (ByteText.ofString name), value_cursor, value_ctx]

/-- Mirrors `find_var_e_global`. -/
def find_var_e_global (call : Call m) (value_ctx : value) (name : String) : m value :=
  find_var_e call Pack.cursorGlobal value_ctx name

/-- Mirrors the local cursor wrapper, with the pinned cursor type note. -/
def find_var_e_local (call : Call m) (value_ctx : value) (name : String) : m value :=
  find_var_e call Pack.cursorLocal value_ctx name

/-- Mirrors `subst_type_e`. -/
def subst_type_e (call : Call m) (value_cursor value_ctx value_typ : value) : m value :=
  call "subst_type_e" [] [value_cursor, value_ctx, value_typ]

/-- Mirrors `subst_type_e_local`. -/
def subst_type_e_local (call : Call m) (value_ctx value_typ : value) : m value :=
  subst_type_e call Pack.cursorLocal value_ctx value_typ

end P4SpecTec.BackendSim.SpecImpl.Func
