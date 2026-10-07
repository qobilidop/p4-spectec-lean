import P4SpecTec.BackendSim.Core.Object
import P4SpecTec.BackendSim.Make
import P4SpecTec.BackendSim.SpecImpl.Pack
import P4SpecTec.BackendSim.SpecImpl.Unpack

/-!
Port of `p4spec/lib/backend-sim/ebpf/object.ml`: the eBPF extern object, the counter
array, with its constructor and methods over the spec trampolines. Counts are OCaml
integers, serialized as JSON integers as `ppx_deriving_yojson` does for `int list`, and
added with the host's 63-bit wraparound. Every upstream exception (a malformed argument, a
missing constructor argument) is the hard error `Fail.err`.
-/

namespace P4SpecTec.BackendSim.Ebpf.Object

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude P4SpecTec.BackendSim.SpecImpl
open P4SpecTec.BackendSim.Core.Object (Error)

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- Mirrors a method's four results: the object, the context, the architecture and the
void call result. -/
abbrev Outcome (α : Type) := α × value × value × value

/-- The `index` or `value` argument of a method as a host integer. -/
def bitArgument (spec : Make.Spec m) (value_ctx : value) (name : String) : m Int := do
  let v ← Func.find_var_e_local spec.func value_ctx name
  let (_, n) ← Func.required (Unpack.unpack_p4_fixedBit v)
  pure n

/-! Mirrors `CounterArray`. -/
namespace CounterArray

/-- Mirrors `t`: one count per index. -/
abbrev t := List Int

/-- Mirrors `to_yojson`. -/
def to_yojson (counts : t) : Lean.Json := .arr (counts.map fun n => Lean.toJson n).toArray

/-- Mirrors `of_yojson`. -/
def of_yojson (json : Lean.Json) : Except Error t := do
  (← json.getArr?.mapError fun _ => .decode).toList.mapM fun j =>
    j.getInt?.mapError fun _ => .decode

/-- Mirrors `init`: `max_index` zero counts; `sparse` is read and ignored. -/
def init (_value_type_args value_ids value_args : value) : m t := do
  let args ← Func.required (Unpack.assoc_args value_ids value_args)
  let value_max_index ← Func.required (Unpack.assoc args "max_index")
  let value_sparse ← Func.required (Unpack.assoc args "sparse")
  let (_, max_index) ← Func.required (Unpack.unpack_p4_fixedBit value_max_index)
  let _ ← Func.required (Unpack.unpack_p4_bool value_sparse)
  pure (List.replicate max_index.toNat 0)

/-- Mirrors `increment`: the count at `index` plus one; an index outside the array changes
nothing. -/
def increment (spec : Make.Spec m) (value_ctx value_sto : value) (counter_array : t) :
    m (Outcome t) := do
  let index ← bitArgument spec value_ctx "index"
  let counter_array := counter_array.mapIdx fun idx count =>
    if (idx : Int) == index then Core.Object.hostAdd count 1 else count
  pure (counter_array, value_ctx, value_sto, Pack.returnVoid)

/-- Mirrors `add`: the count at `index` plus `value`. -/
def add (spec : Make.Spec m) (value_ctx value_sto : value) (counter_array : t) :
    m (Outcome t) := do
  let index ← bitArgument spec value_ctx "index"
  let value ← bitArgument spec value_ctx "value"
  let counter_array := counter_array.mapIdx fun idx count =>
    if (idx : Int) == index then Core.Object.hostAdd count value else count
  pure (counter_array, value_ctx, value_sto, Pack.returnVoid)

end CounterArray

end P4SpecTec.BackendSim.Ebpf.Object
