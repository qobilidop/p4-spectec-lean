import P4SpecTec.Util.ByteText

/-!
Partial port of `p4spec/lib/runtime/sim/io.ml`: port/packet and rx/tx/expect
types only. The print and wildcard STF comparison functions are not ported.
Ports retain signed integers; target boundaries check the pinned signed-63-bit
OCaml domain. Packet strings are arbitrary ByteText, not decoded Unicode.
-/

namespace P4SpecTec.Runtime.Sim.Io

/-- Mirrors the signed OCaml input/output port number. -/
abbrev port := Int

/-- Mirrors packet strings without changing case or replacing their bytes. -/
abbrev packet := ByteText

/-- Mirrors one received port and packet. -/
abbrev rx := port × packet

/-- Mirrors one transmitted port and packet. -/
abbrev tx := port × packet

/-- Mirrors an expected output and the exact-match flag; comparison is not ported. -/
abbrev expect := tx × Bool

end P4SpecTec.Runtime.Sim.Io
