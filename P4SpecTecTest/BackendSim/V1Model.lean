import P4SpecTec.BackendSim.V1Model.Stf

/-!
Unit checks of the v1model port's host-side pieces, against values computed by hand from
the upstream OCaml: the STF name transformations and OCaml string helpers, the packers and
unpackers, the hash algorithms on small inputs, the multicast and mirror maps, and the
architecture state's JSON round trip. Agreement of the pipeline itself with upstream is the
session replay's obligation.
-/

namespace P4SpecTecTest.V1Model

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Runtime P4SpecTec.Lang.Il
open P4SpecTec.BackendSim P4SpecTec.BackendSim.SpecImpl P4SpecTec.BackendSim.V1Model

/-! ## STF transformations -/

#guard Stf.Transform.rewrite_substring ["ingress", "preqos"] "main.ig" "MyIngress.t" == "main.ig.t"
#guard Stf.Transform.rewrite_substring ["egress", "postqos", "c3"] "main.eg" "C3.t" == "main.eg.t"
#guard Stf.Transform.rewrite_substring ["ingress"] "main.ig" "parser.t" == "parser.t"
#guard Stf.Transform.rewrite_substring ["ingress"] "main.ig" "ingress" == "main.ig"
#guard Stf.Transform.rewrite_valid ("hdr.ipv4.$valid$", .Num "1") ==
  ("hdr.ipv4.isValid()", .Num "1")
#guard Stf.Transform.convert_dollar_to_brackets "hdr.stack$2.f" == "hdr.stack[2].f"
#guard Stf.Transform.convert_dollar_to_brackets "a$b$10" == "a$b[10]"
#guard Stf.Transform.escaped "a.b" == "a.b"
#guard Stf.Transform.escaped "a\"b\\c" == "a\\\"b\\\\c"
#guard Stf.Transform.upperAscii "0a0b" == "0A0B"
#guard Stf.Transform.int_of_string "42" == some 42
#guard Stf.Transform.int_of_string "0x1F" == some 31
#guard Stf.Transform.int_of_string "0b101" == some 5
#guard Stf.Transform.int_of_string "-7" == some (-7)
#guard Stf.Transform.int_of_string "1_000" == some 1000
#guard Stf.Transform.int_of_string "x" == none
#guard Stf.Transform.int_of_string "" == none

#guard V1Model.Stf.transform_stf_stmt (.Add "ingress.t" none [("h.$valid$", .Num "1")]
  ("ingress.a", [("p", "1")]) none) ==
  .Add "main.ig.t" none [("h.isValid()", .Num "1")] ("main.ig.a", [("p", "1")]) none
#guard V1Model.Stf.transform_stf_stmt (.Packet "0" "ab") == .Packet "0" "ab"

/-! ## Packing and unpacking -/

#guard Unpack.unpack_p4_fixedBit (Pack.pack_p4_fixedBit 9 511) == some (9, 511)
#guard Unpack.unpack_p4_fixedBit (Pack.pack_p4_arbitraryInt 3) == none
#guard Unpack.unpack_p4_precision_numberValue (Pack.pack_p4_fixedBit 16 7) == some (16, 7)
#guard Unpack.unpack_p4_enum (Pack.pack_p4_enum (ByteText.ofString "CloneType")
  (ByteText.ofString "I2E")) == some (ByteText.ofString "CloneType", ByteText.ofString "I2E")
#guard Unpack.unpack_p4_bool (Pack.pack_p4_fixedBit 1 1) == none
#guard (Unpack.assoc_args (Value.Make.list .TextT [Value.Make.text (ByteText.ofString "size")])
  (Value.Make.list .TextT [Value.Make.nat 4])).isSome
#guard (Unpack.assoc_args (Value.Make.list .TextT [Value.Make.text (ByteText.ofString "size")])
  (Value.Make.list .TextT [])).isNone

/-! ## Hashes -/

-- The 16-bit ones' complement checksum of 0x0001 0x0002 is the complement of 0x0003.
#guard Hash.compute_hash (ByteText.ofString "csum16") 0 (32, 0x00010002) == some 0xFFFC
#guard Hash.compute_hash (ByteText.ofString "identity") 0 (16, 0x1234) == some 0x1234
-- CRC-16/ARC of the single byte 0x01 is 0xC0C1; CRC-32 of 0x00 is 0xD202EF8D.
#guard Hash.compute_hash (ByteText.ofString "crc16") 0 (8, 0x01) == some 0xC0C1
#guard Hash.compute_hash (ByteText.ofString "crc32") 0 (8, 0x00) == some 0xD202EF8D
#guard Hash.compute_hash (ByteText.ofString "md5") 0 (8, 0) == none
#guard Hash.adjust 10 0 123 == some 10
#guard Hash.adjust 10 14 123 == some (123 % 4 + 10)
#guard Hash.adjust 10 5 123 == none
#guard Hash.package [Pack.pack_p4_fixedBit 4 0xA, Pack.pack_p4_fixedBit 4 0x5] == some (16, 0xA5)
#guard Hash.of_two_complement (-1) 8 == 255

/-! ## Multicast and mirror maps -/

#guard (Multicast.IntMap.add 2 "b" (Multicast.IntMap.add 10 "c" (Multicast.IntMap.add 1 "a" []))
  : List (Int × String)) == [(1, "a"), (2, "b"), (10, "c")]
#guard (Multicast.IntMap.add 1 "z" [(1, "a")] : List (Int × String)) == [(1, "z")]
#guard (Multicast.IntMap.update 5 (· ++ "!") [(1, "a")] : List (Int × String)) == [(1, "a")]
#guard (Multicast.State.node_associate 7 3 (Multicast.State.group_create 7
  (Multicast.State.node_create 9 [1, 2] Multicast.State.empty))).groups ==
  [(7, { id := 7, node_handles := [3] })]
#guard (Multicast.State.node_create 9 [1, 2] Multicast.State.empty).next_handle == 1
#guard Mirror.Table.find_opt 3 (Mirror.Table.add 3 8 Mirror.Table.empty) == some 8

/-! ## Architecture state round trip -/

private def sample : Arch.t :=
  Arch.with_clone (.I2E, 3, 1) (Arch.with_mirrortable (Mirror.Table.add 3 8 Mirror.Table.empty)
    (Arch.with_multicast (Multicast.State.node_create 9 [1, 2]
      (Multicast.State.group_create 7 Multicast.State.empty)) Arch.empty))

#guard match Arch.of_value (Arch.to_value sample) with
  | .ok a => Arch.to_yojson a == Arch.to_yojson sample
  | .error _ => false
#guard (Arch.to_yojson Arch.empty).compress ==
  "{\"action\":{\"clone_opt\":null,\"recirculate_opt\":null,\"resubmit_opt\":null},\
  \"mirrortable\":{},\"multicast\":{\"groups\":{},\"next_handle\":0,\"nodes\":{}},\"queue\":[]}"
#guard match Arch.of_value
    (Value.Make.extern (.VarT (Util.Source.mkPhrase "archState") []) .null) with
  | .error _ => true
  | .ok _ => false

/-! ## Statement runner on a trampoline-free statement -/

private abbrev M := ExceptT Fail Id

private def noSpec : Make.Spec M :=
  { func := fun _ _ _ => throw .err, rel := fun _ _ => throw .err }

private def ctx : value := Value.Make.text (ByteText.ofString "ctx")

#guard match (V1Model.Stf.run_stf_stmt noSpec ctx Pipe.init_arch_state .Wait).run with
  | .ok (c, a, txs) => Value.eq c ctx && Value.eq a Pipe.init_arch_state && txs.isEmpty
  | .error _ => false
#guard match (V1Model.Stf.run_stf_stmt noSpec ctx Pipe.init_arch_state .NoPacket).run with
  | .error .err => true
  | _ => false
#guard match (V1Model.Stf.run_stf_stmt noSpec ctx Pipe.init_arch_state
    (.RegisterRead "r" "0")).run with
  | .error .err => true
  | _ => false

end P4SpecTecTest.V1Model
