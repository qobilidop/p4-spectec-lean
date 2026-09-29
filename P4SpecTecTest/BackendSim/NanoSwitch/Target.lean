import P4SpecTec.BackendSim.NanoSwitch.Pipe

/-! Bounded dynamic Nano target tests; pinned differential evidence is a separate obligation. -/

namespace P4SpecTecTest.NanoTarget

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Runtime P4SpecTec.Lang.Il
open P4SpecTec.Util.Source P4SpecTec.BackendSim.Core.Object
open P4SpecTec.BackendSim.NanoSwitch.Pipe

private def ok [BEq α] (r : Except Error α) (v : α) : Bool :=
  match r with | .ok x => x == v | .error _ => false

private def err (r : Except Error α) (e : Error) : Bool :=
  match r with | .error actual => actual == e | .ok _ => false

#guard ok (string_to_bits (ByteText.ofString "a5"))
  #[true, false, true, false, false, true, false, true]
#guard err (string_to_bits (ByteText.ofString "g0")) .assertion
#guard err (string_to_bits (ByteText.ofBytes ⟨#[255]⟩)) .assertion
#guard bits_to_string #[true, false, true] == ByteText.ofString "A"
#guard bits_to_string #[] == ByteText.ofString ""
#guard bits_to_int_unsigned #[true, false, true] == 5
#guard ok (bits_to_int_signed #[true, false, true]) (-3)
#guard err (bits_to_int_signed #[]) .invalidArgument
#guard ok (int_to_bits_signed (-3) 4) #[true, true, false, true]
#guard ok (int_to_bits_unsigned 18 4) #[false, false, true, false]
#guard err (int_to_bits_unsigned 1 (-1)) .invalidArgument

private def inconsistent : PacketIn.t := { bits := #[true, false], idx := 0, len := -1 }
#guard ok (PacketIn.of_yojson (PacketIn.to_yojson inconsistent)) inconsistent
#guard ok (PacketIn.parse inconsistent 1) ({ inconsistent with idx := 1 }, #[true])
#guard err (PacketIn.payload inconsistent) .invalidArgument
#guard err (PacketIn.parse { inconsistent with idx := -1 } 1) .invalidArgument
#guard err (PacketIn.parse inconsistent 3) .invalidArgument
#guard err (PacketIn.of_yojson (.arr #[])) .decode
#guard err (PacketIn.of_yojson (Lean.Json.mkObj
  [("bits", .arr #[]), ("idx", Lean.toJson (2 ^ 62 : Int)), ("len", Lean.toJson (0 : Int))]))
  .hostRange
#guard hostAdd ((2 : Int) ^ 62 - 1) 24 == -((2 : Int) ^ 62) + 23
#guard match PacketIn.init (ByteText.ofString "FF8") >>= PacketIn.payload_bytes with
  | .ok values => values == #[255]
  | .error _ => false

private def receiver (pkt : PacketIn.t) : value := Value.Make.case (varT "value")
  (.Seq [.Atom (mkPhrase (.Keyword "PACKET")),
    .Arg (Value.Make.text (ByteText.ofString "packet_in")),
    .Arg (Value.Make.extern (varT "objectState") (extern_to_yojson (.PacketIn pkt)))])

private def args (pkt : PacketIn.t) : List value :=
  [Value.Make.bool false, receiver pkt, Value.Make.text (ByteText.ofString "extract"),
   Value.Make.list (.IterT (mkPhrase (varT "nameIR")) .List)
     [Value.Make.text (ByteText.ofString "hdr")]]

private def noCallback : Call StateEval := fun _ _ _ => throw .err

private def isNat (v : value) (n : Nat) : Bool :=
  match v.it with | .NumV (.Nat x) => x == n | _ => false

private def callbacks : Call StateEval := fun name types values => do
  if !types.isEmpty then throw .err
  let token ← StateEval.freshTypeId
  match name, values with
  | "find_var_e", [scope, ctx, hdr] =>
    unless token == "FRESH__5" && (Value.Get.bool ctx == some false) &&
        (Value.Get.text hdr == some (ByteText.ofString "hdr")) do throw .err
    let .CaseV (.Atom scopeAtom) := scope.it | throw .err
    unless scopeAtom.it == .Keyword "LOCAL" do throw .err
    pure (Value.Make.nat 10)
  | "write_value_from_bits", [hdr, bs] =>
    unless token == "FRESH__6" && isNat hdr 10 do throw .err
    let some bs := Value.Get.list bs | throw .err
    unless bs.length == 24 && bs.all (fun b => Value.Get.bool b == some true) do throw .err
    pure (Value.Make.nat 42)
  | "update_var_e", [scope, ctx, name, hdr] =>
    let .CaseV (.Atom scopeAtom) := scope.it | throw .err
    unless token == "FRESH__7" && Value.Get.bool ctx == some false &&
        scopeAtom.it == .Keyword "LOCAL" &&
        Value.Get.text name == some (ByteText.ofString "hdr") &&
        isNat hdr 42 do throw .err
    pure (Value.Make.bool true)
  | _, _ => throw .err

private def rawResult (r : Option (Except Fail (List value) × FreshState))
    (idx : Int) (ctx : Bool) (state : FreshState) : Bool :=
  match r with
  | some (.ok [output, context], final) =>
    match output.it with
    | .ExternV json =>
      match extern_of_yojson json with
      | .ok (.PacketIn pkt) =>
        pkt.idx == idx && Value.Get.bool context == some ctx && final == state
      | .error _ => false
    | _ => false
  | _ => false

private def packet : PacketIn.t := { bits := Array.replicate 24 true, idx := 0, len := 24 }

#guard rawResult (StateEval.run (eval_extern_method_call callbacks (args packet)) 5) 24 true 8
#guard rawResult (StateEval.run
  (eval_extern_method_call noCallback (args { packet with len := 23 })) 5) 0 false 5
-- A validly decoded but inconsistent record retains operation-specific behavior.
#guard rawResult (StateEval.run
  (eval_extern_method_call noCallback (args inconsistent)) 5) 0 false 5
-- Compare the whole packet payload with a state-changing callback available.
#guard match StateEval.run (eval_extern_method_call callbacks (args inconsistent)) 5 with
  | some (.ok [output, context], final) =>
    match output.it with
    | .ExternV json => json == extern_to_yojson (.PacketIn inconsistent) &&
        Value.Get.bool context == some false && final == 5
    | _ => false
  | _ => false
-- Wrapped idx+24 is negative, so parse is attempted and rejects the invalid array index.
#guard match StateEval.run (eval_extern_method_call noCallback
    (args { packet with idx := (2 : Int) ^ 62 - 1 })) 5 with
  | some (.error .err, s) => s == 5
  | _ => false
#guard match StateEval.run (eval_extern_method_call
    (fun _ _ _ => do let _ ← StateEval.freshTypeId; throw .unmatch) (args packet)) 5 with
  | some (.error .unmatch, s) => s == 6
  | _ => false
#guard (StateEval.run (eval_extern_method_call
  (fun _ _ _ => ExceptT.mk fun _ => none) (args packet)) 5).isNone
#guard match StateEval.run (eval_extern_method_call noCallback []) 5 with
  | some (.error .err, s) => s == 5
  | _ => false

-- The registered trampoline collapses either callee failure to a mismatch, keeping the
-- callee's post-state, and passes success and divergence through (`Make.call_func`).
private def failing (e : Fail) : Call StateEval := fun _ _ _ => do
  let _ ← StateEval.freshTypeId
  throw e
#guard match StateEval.run (BackendSim.Make.call_func (failing .err) "f" [] []) 5 with
  | some (.error .unmatch, s) => s == 6
  | _ => false
#guard match StateEval.run (BackendSim.Make.call_func (failing .unmatch) "f" [] []) 5 with
  | some (.error .unmatch, s) => s == 6
  | _ => false
#guard match StateEval.run (BackendSim.Make.call_func callbacks "find_var_e" []
    [Value.Make.case (varT "scope") (.Atom (mkPhrase (.Keyword "LOCAL"))),
     Value.Make.bool false, Value.Make.text (ByteText.ofString "hdr")]) 5 with
  | some (.ok v, s) => isNat v 10 && s == 6
  | _ => false
#guard (StateEval.run (BackendSim.Make.call_func (fun _ _ _ => ExceptT.mk fun _ => none)
  "f" [] []) 5).isNone
-- Registered through the interface, a hard callee error makes the extern call a mismatch;
-- the direct handler keeps the callee's own failure kind.
#guard match StateEval.run ((externInterface (m := StateEval)).eval_extern_rel (failing .err)
    "ExternMethodCall_eval" (args packet)) 5 with
  | some (.error .unmatch, s) => s == 6
  | _ => false
#guard match StateEval.run (eval_extern_method_call (failing .err) (args packet)) 5 with
  | some (.error .err, s) => s == 6
  | _ => false
#guard match StateEval.run ((externInterface (m := StateEval)).eval_extern_rel noCallback
    "ExternFunctionCall_eval" []) 5 with
  | some (.error .err, s) => s == 5
  | _ => false

-- Payloads are decoded through their canonical compressed text: a JSON number written with
-- a redundant exponent compresses like the integer, so runtime value equality identifies the
-- two payloads, and the target decodes them alike (design section 5.3).
private def redundantIdx : Lean.Json := .arr #[.str "PacketIn", Lean.Json.mkObj
  [("bits", .arr #[]), ("idx", .num ⟨0, 1⟩), ("len", Lean.toJson (0 : Int))]]
#guard redundantIdx.compress ==
  (extern_to_yojson (.PacketIn { bits := #[], idx := 0, len := 0 })).compress
#guard match extern_of_yojson redundantIdx with | .error _ => true | .ok _ => false
#guard match extern_of_payload redundantIdx with
  | .ok (.PacketIn pkt) => pkt == { bits := #[], idx := 0, len := 0 }
  | .error _ => false
#guard match extern_of_payload (extern_to_yojson (.PacketIn inconsistent)) with
  | .ok (.PacketIn pkt) => pkt == inconsistent
  | .error _ => false

end P4SpecTecTest.NanoTarget
