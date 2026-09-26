import Lean.Data.Json.FromToJson.Basic
import P4SpecTec.Util.ByteText

/-!
Partial port of `p4spec/lib/backend-sim/core/object.ml`: bit conversions and
the data-only PacketIn/PacketOut operations. Spec-dependent methods in the
upstream Make functor are not implemented here. OCaml assertions, array
exceptions and JSON errors are explicit; malformed data is never made empty.
The integer boundary is the pinned 64-bit OCaml signed 63-bit representation.
-/

namespace P4SpecTec.BackendSim.Core.Object

/-- Checked boundary errors; these are not successful empty packets. -/
inductive Error where
  /-- The upstream operation asserts on a nonhexadecimal byte. -/
  | assertion
  /-- The upstream array operation rejects its index or size. -/
  | invalidArgument
  /-- Malformed JSON for the pinned derived representation. -/
  | decode
  /-- A mathematical integer or array outside the pinned OCaml host domain. -/
  | hostRange
  deriving BEq, Repr

/-- Mirrors the array representation of upstream bits. -/
abbrev bits := Array Bool

/-- Check the integer domain of the pinned 64-bit OCaml runtime. -/
def hostInt (n : Int) : Bool := -(2 ^ 62 : Int) ≤ n && n < (2 ^ 62 : Int)

/-- Signed 63-bit addition, including overflow on externally supplied records. -/
def hostAdd (a b : Int) : Int :=
  let n := (a + b) % (2 ^ 63 : Int)
  if n < (2 ^ 62 : Int) then n else n - (2 ^ 63 : Int)

/-- Mirrors the derived boolean-array JSON encoder. -/
def bits_to_yojson (bs : bits) : Lean.Json := .arr (bs.map Lean.Json.bool)

/-- Mirrors the checked boolean-array JSON decoder. -/
def bits_of_yojson (json : Lean.Json) : Except Error bits := do
  let xs ← json.getArr?.mapError fun _ => .decode
  xs.mapM fun x => x.getBool?.mapError fun _ => .decode

/-- Hexadecimal bytes expand most-significant bit first; invalid bytes assert upstream. -/
def string_to_bits (str : ByteText) : Except Error bits := do
  let mut result := #[]
  for c in str.bytes.data do
    let c := c.toNat
    let n ← if 48 ≤ c && c ≤ 57 then pure (c - 48)
      else if 97 ≤ c && c ≤ 102 then pure (c - 97 + 10)
      else if 65 ≤ c && c ≤ 70 then pure (c - 65 + 10)
      else throw .assertion
    result := result ++ #[n / 8 % 2 == 1, n / 4 % 2 == 1, n / 2 % 2 == 1, n % 2 == 1]
  pure result

/-- Render uppercase hexadecimal, right-padding the final short nibble with false bits. -/
def bits_to_string (bs : bits) : ByteText := Id.run do
  let mut result := ByteArray.empty
  for k in List.range ((bs.size + 3) / 4) do
    let mut n := 0
    for j in List.range 4 do
      n := 2 * n + if bs[k * 4 + j]?.getD false then 1 else 0
    result := result.push (UInt8.ofNat (if n < 10 then n + 48 else n - 10 + 65))
  pure (ByteText.ofBytes result)

/-- Mirrors unsigned most-significant-bit-first accumulation into Bigint. -/
def bits_to_int_unsigned (bs : bits) : Int :=
  bs.foldl (fun i bit => i * 2 + if bit then 1 else 0) 0

/-- Mirrors two's-complement decoding; empty input raises an array exception upstream. -/
def bits_to_int_signed (bs : bits) : Except Error Int := do
  let some sign := bs[0]? | throw .invalidArgument
  pure (bits_to_int_unsigned bs - if sign then (2 : Int) ^ bs.size else 0)

/-- Mirror fixed-width low-bit extraction; negative sizes are array errors. -/
def int_to_bits_unsigned (value size : Int) : Except Error bits := do
  if !hostInt size then throw .hostRange
  if size < 0 then throw .invalidArgument
  pure ((List.range size.toNat).reverse.map fun i => (value / (2 : Int) ^ i) % 2 == 1).toArray

/-- Mirrors signed low-bit extraction after the width mask. -/
def int_to_bits_signed (value size : Int) : Except Error bits :=
  int_to_bits_unsigned value size

/-- The checked counterpart of Array.sub; it never uses truncating extraction unchecked. -/
def arraySub (bs : bits) (start count : Int) : Except Error bits := do
  if !hostInt start || !hostInt count || !hostInt bs.size then throw .hostRange
  if start < 0 || count < 0 || start > bs.size || count > bs.size - start then
    throw .invalidArgument
  pure (bs.extract start.toNat (start + count).toNat)

namespace PacketIn

/-- Mirrors PacketIn.t, retaining signed indices and inconsistent decoded lengths. -/
structure t where
  /-- All packet bits, not just the unconsumed payload. -/
  bits : bits
  /-- Current signed cursor. -/
  idx : Int
  /-- Declared signed packet length. -/
  len : Int
  deriving BEq, Repr

/-- Mirrors the derived record encoder. -/
def to_yojson (pkt : t) : Lean.Json := Lean.Json.mkObj
  [("bits", bits_to_yojson pkt.bits), ("idx", Lean.toJson pkt.idx), ("len", Lean.toJson pkt.len)]

/-- Decode fields without normalizing signed indices or imposing length consistency. -/
def of_yojson (json : Lean.Json) : Except Error t := do
  let fields ← json.getObj?.mapError fun _ => .decode
  if fields.toList.length != 3 then throw .decode
  let bits ← bits_of_yojson (← json.getObjVal? "bits" |>.mapError fun _ => .decode)
  let idx ← (← json.getObjVal? "idx" |>.mapError fun _ => .decode).getInt?
    |>.mapError fun _ => .decode
  let len ← (← json.getObjVal? "len" |>.mapError fun _ => .decode).getInt?
    |>.mapError fun _ => .decode
  if !hostInt idx || !hostInt len || !hostInt bits.size then throw .hostRange
  pure { bits, idx, len }

/-- Initialize a packet from hexadecimal bytes. -/
def init (pkt : ByteText) : Except Error t := do
  let bits ← string_to_bits pkt
  if !hostInt bits.size then throw .hostRange
  pure { bits, idx := 0, len := bits.size }

/-- Reset only the cursor, preserving the upstream record's other contents. -/
def reset (pkt : t) : t := { pkt with idx := 0 }

/-- Parse by actual array bounds, not by the possibly inconsistent declared len field. -/
def parse (pkt : t) (size : Int) : Except Error (t × bits) := do
  let bits ← arraySub pkt.bits pkt.idx size
  pure ({ pkt with idx := hostAdd pkt.idx size }, bits)

/-- Extract the declared remaining payload, preserving signed subtraction behavior. -/
def payload (pkt : t) : Except Error bits :=
  arraySub pkt.bits pkt.idx (hostAdd pkt.len (-pkt.idx))

/-- Convert complete payload bytes only; the upstream function drops a short trailing byte. -/
def payload_bytes (pkt : t) : Except Error (Array Int) := do
  let bs ← payload pkt
  pure ((List.range (bs.size / 8)).map fun i =>
    bits_to_int_unsigned (bs.extract (i * 8) (i * 8 + 8))).toArray

end PacketIn

namespace PacketOut

/-- Mirrors the data-only PacketOut record; spec-dependent emit is not ported. -/
structure t where
  /-- Accumulated output bits. -/
  bits : bits
  deriving BEq, Repr

/-- Mirrors the empty output packet initializer. -/
def init : t := { bits := #[] }

end PacketOut
end P4SpecTec.BackendSim.Core.Object
