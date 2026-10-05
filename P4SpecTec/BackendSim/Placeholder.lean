import P4SpecTec.BackendSim.Core.Func
import P4SpecTec.BackendSim.Make
import P4SpecTec.Interp.InterpAl.Interp

/-!
Partial port of `p4spec/lib/backend-sim/placeholder.ml`, with the name dispatch of
`backend-sim/extern.ml`: the target `backend-sim/build.ml` selects when no architecture
is named, and the P4 boot runner's, for typing and instantiation without packet
processing. Its two state initializers return null extern values, the compile-time
extern call implements `static_assert`, and every other extern operation raises. The
mirror-session, multicast and register interfaces, which all raise, and STF handling are
not ported.

As in the NanoSwitch port, operations are generic in the effect carrier, the function
trampoline is an explicit callback registered through `Make.call_func`, and an upstream
`error` is the hard error `Fail.err`.
-/

namespace P4SpecTec.BackendSim.Placeholder

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude
open P4SpecTec.Util.Source

/-- Explicit substitute for the pinned mutable Spec.Func.call trampoline. -/
abbrev Call (m : Type → Type) := SpecImpl.Func.Call m

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- Require a runtime value shape, matching upstream's raising Get accessors. -/
private def required {α : Type} (result : Option α) : m α :=
  match result with | some x => pure x | none => throw .err

/-- Mirrors init_arch_state: the JSON representation of unit. -/
def init_arch_state : value :=
  Value.Make.extern (.VarT (mkPhrase "archState") []) .null

/-- Mirrors eval_extern_init: the arguments are ignored. -/
def eval_extern_init (_values_input : List value) : value :=
  Value.Make.extern (.VarT (mkPhrase "objectState") []) .null

/-- Mirrors eval_extern_func_lctk_call: `static_assert` with or without a message, by its
parameter names; any other compile-time extern call is an error. -/
def eval_extern_func_lctk_call (call : Call m) (values_input : List value) :
    m (List value) := do
  let [value_ctx, value_name_func, value_names_param] := values_input | throw .err
  let name_func ← required (Value.Get.text value_name_func)
  let names_param ← required do (← Value.Get.list value_names_param).mapM Value.Get.text
  let named (names : List String) : Bool := names_param == names.map ByteText.ofString
  unless name_func == ByteText.ofString "static_assert" do throw .err
  if named ["check", "message"] then pure [← Core.Func.static_assert call true value_ctx]
  else if named ["check"] then pure [← Core.Func.static_assert call false value_ctx]
  else throw .err

/-- Mirrors `Extern.Make.eval_extern_rel` over this target: runtime extern function and
method calls are not implemented for the placeholder, and unknown names are errors. -/
def eval_extern_rel (call : Call m) (name : String) (values_input : List value) :
    m (List value) :=
  if name == "ExternFunctionCall_eval_lctk" then eval_extern_func_lctk_call call values_input
  else throw .err

/-- Mirrors `Extern.Make.eval_extern_func` over this target. -/
def eval_extern_func (name : String) (values_input : List value) : m value :=
  if name == "init_objectState" then pure (eval_extern_init values_input)
  else if name == "init_archState" then pure init_arch_state
  else throw .err

/-- The placeholder as the interpreter's extern interface. The interpreter's callback is
registered through `call_func`, collapsing callee failures as upstream does. -/
def externInterface : Interp_al.Interp.Extern m where
  eval_extern_rel := fun call => eval_extern_rel (Make.call_func call)
  eval_extern_func := fun name _ args => eval_extern_func name args

end P4SpecTec.BackendSim.Placeholder
