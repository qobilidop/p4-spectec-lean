import P4SpecTec.BackendSim.Make
import P4SpecTec.BackendSim.Stf.Transform
import P4SpecTec.BackendSim.Table
import P4SpecTec.Runtime.Sim.Io

/-!
Port of the statement runner `run_stf_stmt` of `backend-sim/make.ml`, over a target's
architecture operations (upstream's `ARCH` functor argument), for the statements the pinned
simulators support: packets through `drive_pipe`, table entries and default actions through
the table interface, mirror sessions and multicast groups through the architecture, and
`wait`, `expect` and `mirroring_get`, which change no state. Expectation matching
(`on_tx_output`, `on_tx_expect`) is not ported: a packet's transmissions are returned to the
caller, which compares them with upstream's record. A statement upstream's `error_stf`
rejects, or an interface the target does not implement, is the hard error.
-/

namespace P4SpecTec.BackendSim.Stf.Run

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude P4SpecTec.Util.Source
open P4SpecTec.BackendSim P4SpecTec.BackendSim.SpecImpl

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- The outcome of one statement: the context, the architecture and, for a packet, its
transmissions. -/
abbrev Outcome := value × value × List Runtime.Sim.Io.tx

/-- A target's architecture operations as the statement runner uses them: upstream's `ARCH`
interface, less the extern evaluation and the register interface, which no supported
statement reaches. -/
structure Arch (m : Type → Type) where
  /-- The target's `transform_stf_stmt`. -/
  transform_stf_stmt : Ast.stmt → Ast.stmt
  /-- A received packet through the pipeline, with its transmissions. -/
  drive_pipe : Make.Spec m → value → value → Runtime.Sim.Io.rx → m Outcome
  /-- `mirroring_add`. -/
  add_mirror_session : Make.Spec m → value → Int → Int → m value
  /-- `mc_mgrp_create`. -/
  mc_mgrp_create : Make.Spec m → value → Int → m value
  /-- `mc_node_create`. -/
  mc_node_create : Make.Spec m → value → Int → List Int → m value
  /-- `mc_node_associate`. -/
  mc_node_associate : Make.Spec m → value → Int → Int → m value

/-- OCaml's `int_of_string`, or the hard error. -/
def int_of (s : String) : m Int := Func.required (Transform.int_of_string s)

/-- A text value of a host string. -/
def text (s : String) : value := Value.Make.text (ByteText.ofString s)

/-- The type note of a named interface type. -/
def varT (name : String) : typ' := .VarT (mkPhrase name) []

/-- Mirrors the action encoding of `run_stf_stmt`: `(nameIR, (nameIR, int)*)`. -/
def action_value (action : Ast.action) : m value := do
  let args ← action.2.mapM fun (name, number) => do
    pure (Value.Make.tuple (varT "tableActionArgumentInterface") [text name,
      Value.Make.int (← int_of number)])
  pure (Value.Make.tuple (varT "tableActionInterface") [text action.1,
    Value.Make.list (.IterT (mkPhrase (varT "tableActionArgumentInterface")) .List) args])

/-- Mirrors the key-value encoding of `run_stf_stmt`: hexadecimal, binary and decimal
numbers by their prefix, and a prefix with a mask length. -/
def key_value (kind : Ast.mtchkind) : m value := do
  let mk := fun (tag : String) (args : List (Domain.Mixfix.t value)) =>
    Value.Make.case (varT "tableKeyValueInterface") (.Seq (Pack.tag tag :: args))
  match kind with
  | .Num number =>
    if number.startsWith "0x" then pure (mk "HEX" [.Arg (text (number.drop 2).toString)])
    else if number.startsWith "0b" then pure (mk "BIN" [.Arg (text (number.drop 2).toString)])
    else pure (mk "DEC" [.Arg (text number)])
  | .Slash pfx mask =>
    let mask ← int_of mask
    unless mask ≥ 0 do throw .err
    pure (Value.Make.case (varT "tableKeyValueInterface")
      (.Seq [.Arg (text pfx), Pack.tag "SLASH", .Arg (Value.Make.nat mask.toNat)]))

/-- Mirrors the keyset encoding of `run_stf_stmt`. -/
def keyset_value (mtches : List Ast.mtch) : m value := do
  let keys ← mtches.mapM fun (name, kind) => do
    pure (Value.Make.tuple (varT "tableKeyInterface")
      [text (Transform.convert_dollar_to_brackets name), ← key_value kind])
  pure (Value.Make.list (.IterT (mkPhrase (varT "tableKeyInterface")) .List) keys)

/-- Mirrors `run_stf_stmt`, after the architecture's transformation. -/
def run_stf_stmt (arch : Arch m) (spec : Make.Spec m) (value_ctx value_arch : value)
    (stmt : Ast.stmt) : m Outcome := do
  match arch.transform_stf_stmt stmt with
  | .Packet port_in packet_in =>
    let port_in ← int_of port_in
    let packet_in := ByteText.ofString (Transform.upperAscii packet_in)
    arch.drive_pipe spec value_ctx value_arch (port_in, packet_in)
  | .Expect port _ _ =>
    -- Upstream parses the port before matching, which is not ported.
    let _ ← int_of port
    pure (value_ctx, value_arch, [])
  | .Add table priority mtches action _ =>
    let value_tableName := text (Transform.escaped table)
    let value_priority := Value.Make.opt (.IterT (mkPhrase (.NumT .IntT)) .Opt)
      (priority.map Value.Make.int)
    let value_keyset ← keyset_value mtches
    let value_action ← action_value action
    let value_arch ← Table.add_entry spec.func value_ctx value_arch value_tableName value_priority
      value_keyset value_action
    pure (value_ctx, value_arch, [])
  | .SetDefault table action =>
    let value_action ← action_value action
    let value_arch ← Table.add_default_action spec.func value_ctx value_arch (text table)
      value_action
    pure (value_ctx, value_arch, [])
  | .MirroringAdd session port =>
    let value_arch ← arch.add_mirror_session spec value_arch (← int_of session) (← int_of port)
    pure (value_ctx, value_arch, [])
  | .MirroringGet _ => pure (value_ctx, value_arch, [])
  | .McGroupCreate mgid =>
    pure (value_ctx, ← arch.mc_mgrp_create spec value_arch (← int_of mgid), [])
  | .McNodeCreate rid ports =>
    let ports ← ports.mapM int_of
    pure (value_ctx, ← arch.mc_node_create spec value_arch (← int_of rid) ports, [])
  | .McNodeAssociate mgid handle =>
    pure (value_ctx, ← arch.mc_node_associate spec value_arch (← int_of mgid) (← int_of handle), [])
  | .Wait => pure (value_ctx, value_arch, [])
  -- `mirroring_add_mc`, the register interface, and the statements `error_stf` rejects.
  | _ => throw .err

end P4SpecTec.BackendSim.Stf.Run
