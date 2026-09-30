import NanoP4Target.Packet

/-! Hexadecimal packet text and the packet-state text premise on sample states. -/

namespace P4SpecTecTest.NanoP4TargetPacket

open P4SpecTec P4SpecTec.BackendSim P4SpecTec.BackendSim.NanoSwitch NanoP4Target

#guard hexText [0x00, 0x01, 0x00] == ByteText.ofString "000100"
#guard hexText [0x80, 0x0A, 0xFF] == ByteText.ofString "800AFF"
#guard hexText [] == ByteText.ofString ""
#guard match Core.Object.string_to_bits (hexText [0x0A, 0x5C]) with
  | .ok bits => bits == (bytesBits [0x0A, 0x5C]).toArray
  | .error _ => false
#guard (bytesBits [0x81]) == [true, false, false, false, false, false, false, true]

/-- Whether the compiled JSON text round trip of `pkt`'s state decodes to `pkt`. -/
def roundTrips (pkt : Core.Object.PacketIn.t) : Bool :=
  match Pipe.extern_of_payload (Pipe.extern_to_yojson (.PacketIn pkt)) with
  | .ok (.PacketIn pkt') => pkt' == pkt
  | .error _ => false

-- Sample states, including the host-range limits, negative and inconsistent records, and
-- every STF packet shape of the corpus (empty, short, header-only and longer).
#guard roundTrips { bits := #[], idx := 0, len := 0 }
#guard roundTrips { bits := (bytesBits [0x00, 0x01, 0x00]).toArray, idx := 0, len := 24 }
#guard roundTrips { bits := (bytesBits [0x00, 0x01, 0x00]).toArray, idx := 24, len := 24 }
#guard roundTrips { bits := (bytesBits [0xFF, 0x03]).toArray, idx := 0, len := 16 }
#guard roundTrips { bits := (bytesBits (List.replicate 64 0xA5)).toArray, idx := 8, len := 512 }
#guard roundTrips { bits := #[true], idx := -5, len := 3 }
#guard roundTrips { bits := #[false, true], idx := 2 ^ 62 - 1, len := -(2 ^ 62) }

end P4SpecTecTest.NanoP4TargetPacket
