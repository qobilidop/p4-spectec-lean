import P4SpecTec.BackendSim.Ebpf.Stf
import P4SpecTec.BackendSim.V1Model.Stf
import P4Spec.Refinement.Spec

/-!
Not a mirror. The generated full-P4 library as a target's spec: the ported v1model and
eBPF simulators call back into the spec through name-dispatched trampolines, and here
each name decodes its IL arguments at the generated types, calls the generated definition
and encodes the result, as the placeholder adapter does for `find_var_value_t`. The typed
`Externs` instance runs the same ported extern dispatch over these trampolines, so the
generated leg and the reference leg share one target implementation and differ only in
the semantics they call back into. A value outside the expected generated type is a hard
error, never a repaired value.
-/

namespace P4SpecTecTest.Diff.P4Sessions.Generated

open P4SpecTec P4SpecTec.Prelude P4SpecTec.BackendSim P4SpecTec.BackendSim.SpecImpl
open P4SpecTec.Lang.Il

/-- Fuel for the value decoders, a nesting bound far above any replayed case's depth. -/
def decodeFuel : Nat := 100000000

/-- Decode at the generated type, or fail hard. -/
def decoded {α : Type} [OfValue α] (v : value) : StateEval α :=
  match OfValue.ofValue decodeFuel v with
  | some x => pure x
  | none => throw .err

/-- A generated computation in the carrier. -/
def gen {α : Type} (x : FreshState → Option (Except Fail α × FreshState)) : StateEval α :=
  ExceptT.mk x

/-- The spec functions the target calls back, on the generated library, by name. These
need no extern instance. -/
def func : Func.Call StateEval := fun name _ values => do
  match name, values with
  | "write_value_from_bits", [v, n, bits] => do
    pure (toValue (← gen (P4Spec.«$write_value_from_bits» (← decoded v) (← decoded n)
      (← decoded bits))))
  | "write_bits_from_value", [v] => do
    pure (toValue (← gen (P4Spec.«$write_bits_from_value» (← decoded v))))
  | "bitacc_range_op", [b, h, l] => do
    pure (toValue (← gen (P4Spec.«$bitacc_range_op» (← decoded b) (← decoded h) (← decoded l))))
  | "default", [t] => do pure (toValue (← gen (P4Spec.«$default» (← decoded t))))
  | "cast_op", [t, v] => do pure (toValue (← gen (P4Spec.«$cast_op» (← decoded t) (← decoded v))))
  | "sizeof_minSizeInBits'", [t] => do
    pure (toValue (← gen (P4Spec.«$sizeof_minSizeInBits'» (← decoded t))))
  | "sizeof_maxSizeInBits'", [t] => do
    pure (toValue (← gen (P4Spec.«$sizeof_maxSizeInBits'» (← decoded t))))
  | "key_interface_of_tableObject", [t] => do
    pure (toValue (← gen (P4Spec.«$key_interface_of_tableObject» (← decoded t))))
  | "tableObject_add_entry", [c, t, p, k, a] => do
    pure (toValue (← gen (P4Spec.«$tableObject_add_entry» (← decoded c) (← decoded t)
      (← decoded p) (← decoded k) (← decoded a))))
  | "tableObject_add_default_action", [c, t, a] => do
    pure (toValue (← gen (P4Spec.«$tableObject_add_default_action» (← decoded c) (← decoded t)
      (← decoded a))))
  | "find_object_qualified_e", [a, i] => do
    pure (toValue (← gen (P4Spec.«$find_object_qualified_e» (← decoded a) (← decoded i))))
  | "find_object_unqualified_e", [a, i] => do
    pure (toValue (← gen (P4Spec.«$find_object_unqualified_e» (← decoded a) (← decoded i))))
  | "update_object_qualified_e", [a, i, o] => do
    pure (toValue (← gen (P4Spec.«$update_object_qualified_e» (← decoded a) (← decoded i)
      (← decoded o))))
  | "update_object_unqualified_e", [a, i, o] => do
    pure (toValue (← gen (P4Spec.«$update_object_unqualified_e» (← decoded a) (← decoded i)
      (← decoded o))))
  | "find_objectState_e", [a, i] => do
    pure (toValue (← gen (P4Spec.«$find_objectState_e» (← decoded a) (← decoded i))))
  | "update_objectState_e", [a, i, s] => do
    pure (toValue (← gen (P4Spec.«$update_objectState_e» (← decoded a) (← decoded i)
      (← decoded s))))
  | "find_archState_e", [a] => do pure (toValue (← gen (P4Spec.«$find_archState_e» (← decoded a))))
  | "update_archState_e", [a, s] => do
    pure (toValue (← gen (P4Spec.«$update_archState_e» (← decoded a) (← decoded s))))
  | "find_type_e", [c, e, n] => do
    pure (toValue (← gen (P4Spec.«$find_type_e» (← decoded c) (← decoded e) (← decoded n))))
  | "find_var_e", [n, c, e] => do
    pure (toValue (← gen (P4Spec.«$find_var_e» (← decoded n) (← decoded c) (← decoded e))))
  | "subst_type_e", [c, e, t] => do
    pure (toValue (← gen (P4Spec.«$subst_type_e» (← decoded c) (← decoded e) (← decoded t))))
  | "find_var_value_t", [n, c, t] => do
    pure (toValue (← gen (P4Spec.«$find_var_value_t» (← decoded n) (← decoded c) (← decoded t))))
  | _, _ => throw .err

/-- The storage relations the target's externs call back, which need no extern instance. -/
def externRel : Rel.RelCall StateEval := fun name values => do
  match name, values with
  | "Lvalue_read", [c, e, a, r] => do
    pure [toValue (← gen (P4Spec.Lvalue_read.run (← decoded c) (← decoded e) (← decoded a)
      (← decoded r)))]
  | "Lvalue_write", [c, e, a, r, v] => do
    pure [toValue (← gen (P4Spec.Lvalue_write.run (← decoded c) (← decoded e) (← decoded a)
      (← decoded r) (← decoded v)))]
  | _, _ => throw .err

/-- The trampolines the externs see, registered as upstream registers them: a failed callee
is a mismatch of the extern call. -/
def externSpec : Make.Spec StateEval :=
  { func := Make.call_func func, rel := Make.call_rel externRel }

section V1Model

/-- The v1model externs for the generated full-P4 library: the ported dispatch over the
generated callbacks, with its IL arguments and results encoded and decoded at the
generated types. Local to this section: the generated relations below take it. -/
@[instance_reducible] def v1modelExterns : P4Spec.Externs where
  ExternFunctionCall_eval_lctk := fun ctx name parameters => StateEval.run do
    let [value] ← V1Model.Pipe.eval_extern_rel externSpec "ExternFunctionCall_eval_lctk"
      [toValue ctx, toValue name, toValue parameters] | throw .err
    decoded value
  «$init_objectState» := fun name targs ids args => StateEval.run do
    decoded (← V1Model.Pipe.eval_extern_init externSpec
      [toValue name, toValue targs, toValue ids, toValue args])
  «$init_archState» := StateEval.run (decoded V1Model.Pipe.init_arch_state)
  ExternFunctionCall_eval := fun ctx arch name parameters => StateEval.run do
    let [c, a, r] ← V1Model.Pipe.eval_extern_rel externSpec "ExternFunctionCall_eval"
      [toValue ctx, toValue arch, toValue name, toValue parameters] | throw .err
    pure (← decoded c, ← decoded a, ← decoded r)
  ExternMethodCall_eval := fun ctx arch objectId name parameters => StateEval.run do
    let [c, a, r] ← V1Model.Pipe.eval_extern_rel externSpec "ExternMethodCall_eval"
      [toValue ctx, toValue arch, toValue objectId, toValue name, toValue parameters] | throw .err
    pure (← decoded c, ← decoded a, ← decoded r)

attribute [local instance] v1modelExterns

set_option maxHeartbeats 4000000 in
/-- The v1model pipeline relations the driver calls, on the generated library with the
typed externs above, and the storage relations. The dispatch is large for the compiler. -/
def rel : Rel.RelCall StateEval := fun name values => do
  let block := fun {ρ : Type} [ToValue ρ] (run : P4Spec.evalContext → P4Spec.arch → FreshState →
      Option (Except Fail (P4Spec.evalContext × (P4Spec.arch × ρ)) × FreshState))
      (c a : value) => do
    let (ctx, arch, result) ← gen (run (← decoded c) (← decoded a))
    pure [toValue ctx, toValue arch, toValue result]
  match name, values with
  | "V1Model_init", [p] => do
    let (ctx, arch) ← gen (P4Spec.V1Model_init.run (← decoded p))
    pure [toValue ctx, toValue arch]
  | "V1Model_init_packet_in", [c, a, s] => do
    let (ctx, arch) ← gen (P4Spec.V1Model_init_packet_in.run (← decoded c) (← decoded a)
      (← decoded s))
    pure [toValue ctx, toValue arch]
  | "V1Model_init_packet_out", [c, a, s] => do
    let (ctx, arch) ← gen (P4Spec.V1Model_init_packet_out.run (← decoded c) (← decoded a)
      (← decoded s))
    pure [toValue ctx, toValue arch]
  | "V1Model_init_globals", [c, a, p] => do
    pure [toValue (← gen (P4Spec.V1Model_init_globals.run (← decoded c) (← decoded a)
      (← decoded p)))]
  | "V1Model_parser", [c, a] => block P4Spec.V1Model_parser.run c a
  | "V1Model_verify", [c, a] => block P4Spec.V1Model_verify.run c a
  | "V1Model_ingress", [c, a] => block P4Spec.V1Model_ingress.run c a
  | "V1Model_egress", [c, a] => block P4Spec.V1Model_egress.run c a
  | "V1Model_check", [c, a] => block P4Spec.V1Model_check.run c a
  | "V1Model_deparse", [c, a] => block P4Spec.V1Model_deparse.run c a
  | "V1Model_setup_preserved_meta_fields", [c, a, i] => do
    pure [toValue (← gen (P4Spec.V1Model_setup_preserved_meta_fields.run (← decoded c)
      (← decoded a) (← decoded i)))]
  | _, _ => externRel name values

/-- The v1model driver's trampolines over the generated library, with upstream's failure
collapse. -/
def spec : Make.Spec StateEval := { func := Make.call_func func, rel := Make.call_rel rel }

end V1Model

section Ebpf

/-- The eBPF externs for the generated full-P4 library, over the same trampolines. -/
@[instance_reducible] def ebpfExterns : P4Spec.Externs where
  ExternFunctionCall_eval_lctk := fun ctx name parameters => StateEval.run do
    let [value] ← Ebpf.Pipe.eval_extern_rel externSpec "ExternFunctionCall_eval_lctk"
      [toValue ctx, toValue name, toValue parameters] | throw .err
    decoded value
  «$init_objectState» := fun name targs ids args => StateEval.run do
    decoded (← Ebpf.Pipe.eval_extern_init [toValue name, toValue targs, toValue ids, toValue args])
  «$init_archState» := StateEval.run (decoded Ebpf.Pipe.init_arch_state)
  ExternFunctionCall_eval := fun ctx arch name parameters => StateEval.run do
    let [c, a, r] ← Ebpf.Pipe.eval_extern_rel externSpec "ExternFunctionCall_eval"
      [toValue ctx, toValue arch, toValue name, toValue parameters] | throw .err
    pure (← decoded c, ← decoded a, ← decoded r)
  ExternMethodCall_eval := fun ctx arch objectId name parameters => StateEval.run do
    let [c, a, r] ← Ebpf.Pipe.eval_extern_rel externSpec "ExternMethodCall_eval"
      [toValue ctx, toValue arch, toValue objectId, toValue name, toValue parameters] | throw .err
    pure (← decoded c, ← decoded a, ← decoded r)

attribute [local instance] ebpfExterns

set_option maxHeartbeats 4000000 in
/-- The eBPF pipeline relations the driver calls, on the generated library with the eBPF
externs, and the storage relations. The dispatch is large for the compiler. -/
def ebpfRel : Rel.RelCall StateEval := fun name values => do
  match name, values with
  | "EBPF_init", [p] => do
    let (ctx, arch) ← gen (P4Spec.EBPF_init.run (← decoded p))
    pure [toValue ctx, toValue arch]
  | "EBPF_init_packet_in", [c, a, s] => do
    let (ctx, arch) ← gen (P4Spec.EBPF_init_packet_in.run (← decoded c) (← decoded a)
      (← decoded s))
    pure [toValue ctx, toValue arch]
  | "EBPF_init_globals", [c, a] => do
    pure [toValue (← gen (P4Spec.EBPF_init_globals.run (← decoded c) (← decoded a)))]
  | "EBPF_parse", [c, a] => do
    let (ctx, arch, result) ← gen (P4Spec.EBPF_parse.run (← decoded c) (← decoded a))
    pure [toValue ctx, toValue arch, toValue result]
  | "EBPF_filter", [c, a] => do
    let (ctx, arch, result) ← gen (P4Spec.EBPF_filter.run (← decoded c) (← decoded a))
    pure [toValue ctx, toValue arch, toValue result]
  | _, _ => externRel name values

/-- The eBPF driver's trampolines over the generated library. -/
def ebpfSpec : Make.Spec StateEval :=
  { func := Make.call_func func, rel := Make.call_rel ebpfRel }

end Ebpf

end P4SpecTecTest.Diff.P4Sessions.Generated
