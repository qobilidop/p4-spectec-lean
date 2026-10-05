import P4SpecTec.Runtime.Value.Value
import P4SpecTec.Prelude.StateEval

/-!
Partial port of `p4spec/lib/backend-sim/spec_impl/func.ml`: only find_var_e,
find_var_value_t and their local wrappers. The mutable function trampoline is an explicit
callback in the caller's effect carrier. This is the pinned full-P4 prefixed-name/cursor ABI,
not Nano's distinct scope/context/name ABI. Other wrappers are not ported.
-/

namespace P4SpecTec.BackendSim.SpecImpl.Func

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude P4SpecTec.Util.Source

/-- Explicit counterpart of the mutable Spec.Func.call trampoline. -/
abbrev Call (m : Type → Type) := String → List typ → List value → m value

variable {m : Type → Type}

/-- Mirrors find_var_e, including prefixed name construction and argument order. -/
def find_var_e (call : Call m) (value_cursor value_ctx : value) (name : String) :
    m value :=
  let value_nameIR := Value.Make.text (ByteText.ofString name)
  let value_prefixedNameIR := Value.Make.case (.VarT (mkPhrase "prefixedNameIR") [])
    (.Seq [.Atom (mkPhrase (.Tag "BARE")), .Arg value_nameIR])
  call "find_var_e" [] [value_prefixedNameIR, value_cursor, value_ctx]

/-- Mirrors the local cursor wrapper, with the pinned cursor type note. -/
def find_var_e_local (call : Call m) (value_ctx : value) (name : String) : m value :=
  let value_cursor := Value.Make.case (.VarT (mkPhrase "cursor") [])
    (.Atom (mkPhrase (.Keyword "LOCAL")))
  find_var_e call value_cursor value_ctx name

/-- Mirrors find_var_value_t, the typing-context lookup, with the same name construction
and argument order as find_var_e. -/
def find_var_value_t (call : Call m) (value_cursor value_ctx : value) (name : String) :
    m value :=
  let value_nameIR := Value.Make.text (ByteText.ofString name)
  let value_prefixedNameIR := Value.Make.case (.VarT (mkPhrase "prefixedNameIR") [])
    (.Seq [.Atom (mkPhrase (.Tag "BARE")), .Arg value_nameIR])
  call "find_var_value_t" [] [value_prefixedNameIR, value_cursor, value_ctx]

/-- Mirrors find_var_value_t_local, with the pinned cursor type note. -/
def find_var_value_t_local (call : Call m) (value_ctx : value) (name : String) : m value :=
  let value_cursor := Value.Make.case (.VarT (mkPhrase "cursor") [])
    (.Atom (mkPhrase (.Keyword "LOCAL")))
  find_var_value_t call value_cursor value_ctx name

end P4SpecTec.BackendSim.SpecImpl.Func
