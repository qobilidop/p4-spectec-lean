import Lean.Data.Json.FromToJson.Basic
import P4SpecTec.Util.ByteText
import P4SpecTec.BackendSim.Make
import P4SpecTec.BackendSim.SpecImpl.Unpack

/-!
Port of `p4spec/lib/backend-sim/core/object.ml`: bit conversions, the data-only
PacketIn/PacketOut operations, and the spec-dependent packet methods of the upstream
Make functor (`extract`, `extract_varsize`, `lookahead`, `advance`, `length`, `emit`),
over explicit function and relation trampolines. OCaml assertions, array exceptions and
JSON errors are explicit; malformed data is never made empty. The integer boundary is
the pinned 64-bit OCaml signed 63-bit representation.
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

/-! ## Spec-dependent methods (the upstream `Make` functor) -/

namespace Spec

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude P4SpecTec.Util.Source
open P4SpecTec.BackendSim.SpecImpl

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- Target-local malformed values are hard errors, never retryable mismatches. -/
def checked {ε α : Type} (result : Except ε α) : m α :=
  match result with | .ok x => pure x | .error _ => throw .err

/-- The outcome of a packet method: the object, the context, the architecture and the call
result, as upstream returns them. -/
abbrev Outcome (α : Type) := α × value × value × value

/-- The size in bits of the local type parameter `T`, substituted in the context. -/
def sizeOfT (spec : Make.Spec m) (value_ctx : value) : m (value × Int) := do
  let value_typ ← Func.find_type_e_local spec.func value_ctx (ByteText.ofString "T")
  let size ← Func.sizeof_maxSizeInBits' spec.func
    (← Func.subst_type_e_local spec.func value_ctx value_typ)
  pure (value_typ, size)

/-- Mirrors `PacketIn.extract`: `void extract<T>(out T hdr)`. -/
def extract (spec : Make.Spec m) (value_ctx value_arch : value) (pkt : PacketIn.t) :
    m (Outcome PacketIn.t) := do
  let (_, size) ← sizeOfT spec value_ctx
  if hostAdd pkt.idx size > pkt.len then
    pure (pkt, value_ctx, value_arch, Pack.rejectError "PacketTooShort")
  else
    let (pkt, bits) ← checked (PacketIn.parse pkt size)
    let value_hdr ← Func.find_var_e_local spec.func value_ctx "hdr"
    let value_hdr ← Func.write_value_from_bits spec.func value_hdr 0 bits
    let value_ctx ← Rel.lvalue_write_var_local spec.rel value_ctx value_arch
      (ByteText.ofString "hdr") value_hdr
    pure (pkt, value_ctx, value_arch, Pack.returnVoid)

/-- Mirrors `PacketIn.extract_varsize`:
`void extract<T>(out T variableSizeHeader, in bit<32> variableFieldSizeInBits)`. -/
def extract_varsize (spec : Make.Spec m) (value_ctx value_arch : value) (pkt : PacketIn.t) :
    m (Outcome PacketIn.t) := do
  let value_typ ← Func.find_type_e_local spec.func value_ctx (ByteText.ofString "T")
  let value_typ_subst ← Func.subst_type_e_local spec.func value_ctx value_typ
  let size_min ← Func.sizeof_minSizeInBits' spec.func value_typ_subst
  let size_max ← Func.sizeof_maxSizeInBits' spec.func value_typ_subst
  let value_variableFieldSizeInBits ← Func.find_var_e_local spec.func value_ctx
    "variableFieldSizeInBits"
  let alignment ← Func.bitacc_range_op spec.func value_variableFieldSizeInBits
    (Pack.pack_p4_arbitraryInt 2) (Pack.pack_p4_arbitraryInt 0)
  let alignment ← Func.required ((Unpack.unpack_p4_fixedBit alignment).map (·.2))
  -- Upstream reads the second mixfix argument of the value as its number.
  let size_varsize ← do
    let c ← Func.required (Value.Get.case value_variableFieldSizeInBits)
    let n ← Func.required ((Domain.Mixfix.args c)[1]?)
    Func.integer n
  let size := size_min + size_varsize
  if alignment != 0 then
    pure (pkt, value_ctx, value_arch, Pack.rejectError "ParserInvalidArgument")
  else if hostAdd pkt.idx size > pkt.len then
    pure (pkt, value_ctx, value_arch, Pack.rejectError "PacketTooShort")
  else if size > size_max then
    pure (pkt, value_ctx, value_arch, Pack.rejectError "HeaderTooShort")
  else
    let (pkt, bits) ← checked (PacketIn.parse pkt size)
    let value_hdr ← Func.find_var_e_local spec.func value_ctx "variableSizeHeader"
    unless hostInt size_varsize && size_varsize ≥ 0 do throw .err
    let value_hdr ← Func.write_value_from_bits spec.func value_hdr size_varsize.toNat bits
    let value_ctx ← Rel.lvalue_write_var_local spec.rel value_ctx value_arch
      (ByteText.ofString "variableSizeHeader") value_hdr
    pure (pkt, value_ctx, value_arch, Pack.returnVoid)

/-- Mirrors `PacketIn.lookahead`: `T lookahead<T>()`. -/
def lookahead (spec : Make.Spec m) (value_ctx value_arch : value) (pkt : PacketIn.t) :
    m (Outcome PacketIn.t) := do
  let (value_typ, size) ← sizeOfT spec value_ctx
  let value_hdr ← Func.default spec.func value_typ
  if hostAdd pkt.idx size > pkt.len then
    pure (pkt, value_ctx, value_arch, Pack.rejectError "PacketTooShort")
  else
    let (_, bits) ← checked (PacketIn.parse pkt size)
    let value_hdr ← Func.write_value_from_bits spec.func value_hdr 0 bits
    pure (pkt, value_ctx, value_arch, Pack.returnValue value_hdr)

/-- Mirrors `PacketIn.advance`: `void advance(in bit<32> sizeInBits)`. -/
def advance (spec : Make.Spec m) (value_ctx value_arch : value) (pkt : PacketIn.t) :
    m (Outcome PacketIn.t) := do
  let value_sizeInBits ← Func.find_var_e_local spec.func value_ctx "sizeInBits"
  let size ← Func.required ((Unpack.unpack_p4_fixedBit value_sizeInBits).map (·.2))
  if hostAdd pkt.idx size > pkt.len then
    pure (pkt, value_ctx, value_arch, Pack.rejectError "PacketTooShort")
  else
    pure ({ pkt with idx := hostAdd pkt.idx size }, value_ctx, value_arch, Pack.returnVoid)

/-- Mirrors `PacketIn.length`: `bit<32> length()`, in whole bytes rounded up. -/
def length (value_ctx value_arch : value) (pkt : PacketIn.t) : m (Outcome PacketIn.t) := do
  let len := pkt.len
  let length := if len % 8 == 0 then len / 8 else len / 8 + 1
  pure (pkt, value_ctx, value_arch, Pack.returnValue (Pack.pack_p4_fixedBit 32 length))

/-- Mirrors `PacketOut.emit`: `void emit<T>(in T hdr)`. -/
def emit (spec : Make.Spec m) (value_ctx value_arch : value) (pkt : PacketOut.t) :
    m (Outcome PacketOut.t) := do
  let value_hdr ← Func.find_var_e_local spec.func value_ctx "hdr"
  let bits ← Func.write_bits_from_value spec.func value_hdr
  let bits ← Func.required ((← Func.required (Value.Get.list bits)).mapM Value.Get.bool)
  pure ({ bits := pkt.bits ++ bits.toArray }, value_ctx, value_arch, Pack.returnVoid)

/-- Mirrors `Packet.pp`: the output bits followed by the input's remaining payload, as
uppercase hexadecimal. -/
def packet (pkt_in : PacketIn.t) (pkt_out : PacketOut.t) : Except Error ByteText := do
  let payload ← arraySub pkt_in.bits pkt_in.idx (hostAdd pkt_in.len (-pkt_in.idx))
  pure (bits_to_string (pkt_out.bits ++ payload))

end Spec

end P4SpecTec.BackendSim.Core.Object
