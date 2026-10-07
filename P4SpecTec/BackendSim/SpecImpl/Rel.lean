import P4SpecTec.BackendSim.SpecImpl.Pack
import P4SpecTec.Prelude.StateEval
import P4SpecTec.Runtime.Sim.Io

/-!
Port of `p4spec/lib/backend-sim/spec_impl/rel.ml`: the helpers that call relations of
the spec through the trampoline registered at initialization, here an explicit `RelCall`
in the target's effect carrier. Each helper builds upstream's argument values and reads
the outputs by arity; an arity upstream asserts on is the hard error `Fail.err`. The
v1model, eBPF and PSA relations are ported; NanoSwitch's are in its pipe.
-/

namespace P4SpecTec.BackendSim.SpecImpl.Rel

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude

/-- Explicit counterpart of the mutable `Spec.Rel.call` trampoline. -/
abbrev RelCall (m : Type → Type) := String → List value → m (List value)

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- The one output of a relation. -/
def one (outputs : List value) : m value :=
  match outputs with | [v] => pure v | _ => throw .err

/-- The two outputs of a relation. -/
def two (outputs : List value) : m (value × value) :=
  match outputs with | [a, b] => pure (a, b) | _ => throw .err

/-- The three outputs of a relation. -/
def three (outputs : List value) : m (value × value × value) :=
  match outputs with | [a, b, c] => pure (a, b, c) | _ => throw .err

/-! ## Lvalue_read -/

/-- Mirrors `lvalue_read_var`. -/
def lvalue_read_var (call : RelCall m) (value_cursor value_ctx value_arch : value)
    (name : ByteText) : m value := do
  one (← call "Lvalue_read" [value_cursor, value_ctx, value_arch, Pack.bareName name])

/-- Mirrors `lvalue_read_var_global`. -/
def lvalue_read_var_global (call : RelCall m) (value_ctx value_arch : value) (name : ByteText) :
    m value :=
  lvalue_read_var call Pack.cursorGlobal value_ctx value_arch name

/-- Mirrors `lvalue_read_dot`. -/
def lvalue_read_dot (call : RelCall m) (value_cursor value_ctx value_arch : value)
    (name member : ByteText) : m value := do
  one (← call "Lvalue_read"
    [value_cursor, value_ctx, value_arch, Pack.dotReference (Pack.bareName name) member])

/-- Mirrors `lvalue_read_dot_global`. -/
def lvalue_read_dot_global (call : RelCall m) (value_ctx value_arch : value)
    (name member : ByteText) : m value :=
  lvalue_read_dot call Pack.cursorGlobal value_ctx value_arch name member

/-! ## Lvalue_write -/

/-- Mirrors `lvalue_write_var`. -/
def lvalue_write_var (call : RelCall m) (value_cursor value_ctx value_arch : value)
    (name : ByteText) (value_val : value) : m value := do
  one (← call "Lvalue_write" [value_cursor, value_ctx, value_arch, Pack.bareName name, value_val])

/-- Mirrors `lvalue_write_dot`. -/
def lvalue_write_dot (call : RelCall m) (value_cursor value_ctx value_arch : value)
    (name member : ByteText) (value_val : value) : m value := do
  one (← call "Lvalue_write" [value_cursor, value_ctx, value_arch,
    Pack.dotReference (Pack.bareName name) member, value_val])

/-- Mirrors `lvalue_write_var_local`. -/
def lvalue_write_var_local (call : RelCall m) (value_ctx value_arch : value) (name : ByteText)
    (value_val : value) : m value :=
  lvalue_write_var call Pack.cursorLocal value_ctx value_arch name value_val

/-- Mirrors `lvalue_write_dot_global`. -/
def lvalue_write_dot_global (call : RelCall m) (value_ctx value_arch : value)
    (name member : ByteText) (value_val : value) : m value :=
  lvalue_write_dot call Pack.cursorGlobal value_ctx value_arch name member value_val

/-- Mirrors `lvalue_write_dot_local`. -/
def lvalue_write_dot_local (call : RelCall m) (value_ctx value_arch : value)
    (name member : ByteText) (value_val : value) : m value :=
  lvalue_write_dot call Pack.cursorLocal value_ctx value_arch name member value_val

/-! ## V1Model -/

/-- A relation of the context, the architecture and a state returning both updated. -/
private def initWith (call : RelCall m) (relation : String) (value_ctx value_arch extra : value) :
    m (value × value) := do
  two (← call relation [value_ctx, value_arch, extra])

/-- A pipeline block relation returning the context, the architecture and a call result. -/
private def block (call : RelCall m) (relation : String) (value_ctx value_arch : value) :
    m (value × value × value) := do
  three (← call relation [value_ctx, value_arch])

/-- Mirrors `v1model_init_packet_in`. -/
def v1model_init_packet_in (call : RelCall m) (value_ctx value_arch value_packet_in_state : value) :
    m (value × value) :=
  initWith call "V1Model_init_packet_in" value_ctx value_arch value_packet_in_state

/-- Mirrors `v1model_init_packet_out`. -/
def v1model_init_packet_out (call : RelCall m)
    (value_ctx value_arch value_packet_out_state : value) : m (value × value) :=
  initWith call "V1Model_init_packet_out" value_ctx value_arch value_packet_out_state

/-- Mirrors `v1model_init_globals`. -/
def v1model_init_globals (call : RelCall m) (value_ctx value_arch : value)
    (port : Runtime.Sim.Io.port) : m value := do
  one (← call "V1Model_init_globals" [value_ctx, value_arch, Value.Make.int port])

/-- Mirrors `v1model_parser`. -/
def v1model_parser (call : RelCall m) (value_ctx value_arch : value) : m (value × value × value) :=
  block call "V1Model_parser" value_ctx value_arch

/-- Mirrors `v1model_verify`. -/
def v1model_verify (call : RelCall m) (value_ctx value_arch : value) : m (value × value × value) :=
  block call "V1Model_verify" value_ctx value_arch

/-- Mirrors `v1model_ingress`. -/
def v1model_ingress (call : RelCall m) (value_ctx value_arch : value) :
    m (value × value × value) :=
  block call "V1Model_ingress" value_ctx value_arch

/-- Mirrors `v1model_egress`. -/
def v1model_egress (call : RelCall m) (value_ctx value_arch : value) : m (value × value × value) :=
  block call "V1Model_egress" value_ctx value_arch

/-- Mirrors `v1model_check`. -/
def v1model_check (call : RelCall m) (value_ctx value_arch : value) : m (value × value × value) :=
  block call "V1Model_check" value_ctx value_arch

/-- Mirrors `v1model_deparse`. -/
def v1model_deparse (call : RelCall m) (value_ctx value_arch : value) :
    m (value × value × value) :=
  block call "V1Model_deparse" value_ctx value_arch

/-- Mirrors `v1model_setup_preserved_meta_fields`. -/
def v1model_setup_preserved_meta_fields (call : RelCall m)
    (value_ctx value_arch value_index : value) :
    m value := do
  one (← call "V1Model_setup_preserved_meta_fields" [value_ctx, value_arch, value_index])

/-! ## EBPF -/

/-- Mirrors `ebpf_init_packet_in`. -/
def ebpf_init_packet_in (call : RelCall m) (value_ctx value_arch value_packet_in_state : value) :
    m (value × value) :=
  initWith call "EBPF_init_packet_in" value_ctx value_arch value_packet_in_state

/-- Mirrors `ebpf_init_globals`. -/
def ebpf_init_globals (call : RelCall m) (value_ctx value_arch : value) : m value := do
  one (← call "EBPF_init_globals" [value_ctx, value_arch])

/-- Mirrors `ebpf_parse`. -/
def ebpf_parse (call : RelCall m) (value_ctx value_arch : value) : m (value × value × value) :=
  block call "EBPF_parse" value_ctx value_arch

/-- Mirrors `ebpf_filter`. -/
def ebpf_filter (call : RelCall m) (value_ctx value_arch : value) : m (value × value × value) :=
  block call "EBPF_filter" value_ctx value_arch

end P4SpecTec.BackendSim.SpecImpl.Rel
