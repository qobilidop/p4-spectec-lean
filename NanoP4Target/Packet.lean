import P4SpecTec.BackendSim.NanoSwitch.Pipe

/-!
# NanoP4Target.Packet

Packet inputs for whole-program statements, and the one trusted boundary of packet decoding.
Not an upstream mirror.

STF packets reach the driver as hexadecimal text. `hexText` writes bytes as uppercase
hexadecimal, and `string_to_bits_hexText` proves that the driver's hexadecimal decoding
(`Core.Object.string_to_bits`, upstream's `string_to_bits`) yields their bits, most
significant first, for every byte list.

Extract decodes the packet state the driver created through its compressed JSON text, as the
target port must (design section 5.3: payloads are identified by their text). Both
`Lean.Json.compress` and `Lean.Json.parse` are `partial`, so Lean's logic cannot compute that
text round trip. `PacketStateText` states it for every packet state within the host integer
range: a named premise of every theorem that runs extract, checked on sample states below and
exercised by the session replay, and never an axiom.
-/

namespace NanoP4Target

open P4SpecTec P4SpecTec.BackendSim P4SpecTec.BackendSim.NanoSwitch

/-- The uppercase hexadecimal digit of a nibble. -/
def hexDigit (n : Nat) : UInt8 := UInt8.ofNat (if n < 10 then 48 + n else 55 + n)

/-- The two hexadecimal digits of a byte, most significant first. -/
def hexDigits (b : UInt8) : List UInt8 := [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- Bytes as uppercase hexadecimal text, the packet form the driver takes. -/
def hexText (bs : List UInt8) : ByteText := ByteText.ofBytes ⟨(bs.flatMap hexDigits).toArray⟩

/-- A nibble's bits, most significant first, as `string_to_bits` expands a digit. -/
def nibbleBits (n : Nat) : List Bool := [n / 8 % 2 == 1, n / 4 % 2 == 1, n / 2 % 2 == 1, n % 2 == 1]

/-- The bits of bytes, most significant first. -/
def bytesBits : List UInt8 → List Bool
  | [] => []
  | b :: bs => nibbleBits (b.toNat / 16) ++ nibbleBits (b.toNat % 16) ++ bytesBits bs

/-- A decoding loop whose step appends the bits of each hexadecimal digit yields the bits of
the bytes. -/
private theorem forIn_hexDigits {ε : Type}
    {f : UInt8 → Array Bool → Except ε (ForInStep (Array Bool))}
    (hf : ∀ n, n < 16 → ∀ acc, f (hexDigit n) acc = .ok (.yield (acc ++ (nibbleBits n).toArray))) :
    ∀ (bs : List UInt8) (acc : Array Bool),
      forIn (bs.flatMap hexDigits) acc f = .ok (acc ++ (bytesBits bs).toArray)
  | [], acc => by simp [bytesBits]; rfl
  | b :: bs, acc => by
    have hi : b.toNat / 16 < 16 := Nat.div_lt_of_lt_mul (by simpa using b.toNat_lt)
    have lo : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    simp only [List.flatMap_cons, hexDigits, List.cons_append, List.nil_append, List.forIn_cons,
      hf _ hi, hf _ lo, forIn_hexDigits hf bs, bytesBits]
    simp [bind, Except.bind, Array.append_assoc]

/-- The driver's hexadecimal decoding of `hexText` yields the bits of the bytes. -/
theorem string_to_bits_hexText (bs : List UInt8) :
    Core.Object.string_to_bits (hexText bs) = .ok (bytesBits bs).toArray := by
  unfold Core.Object.string_to_bits hexText ByteText.ofBytes
  simp only [List.forIn_toArray]
  rw [forIn_hexDigits (fun n h acc => ?_) bs #[]]
  · simp
  · match n, h with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _
    | 12, _ | 13, _ | 14, _ | 15, _ => rfl
    | n + 16, h => exact absurd h (Nat.not_lt_of_le (Nat.le_add_left 16 n))

/-- The unsigned integer of a byte's bits is the byte's value. -/
theorem bits_to_int_unsigned_bytesBits (b : UInt8) :
    Builtin.Numerics.bits_to_int_unsigned (nibbleBits (b.toNat / 16) ++ nibbleBits (b.toNat % 16)) =
      b.toNat := by
  have h : b.toNat < 256 := b.toNat_lt
  generalize b.toNat = n at h ⊢
  revert n
  decide +kernel

/-- The trusted text boundary of packet decoding: the driver's packet state, printed by Lean's
`Json.compress` and parsed back by `Json.parse` in extract, decodes to the same packet for every
state within the host integer range. Both functions are `partial`, so this is a named premise
about Lean's compiled JSON library, not a theorem; `P4SpecTecTest/NanoP4Target/Packet.lean` tests
it on sample states and the session replay exercises it on every corpus packet. -/
def PacketStateText : Prop :=
  ∀ pkt : Core.Object.PacketIn.t, Core.Object.hostInt pkt.idx = true →
    Core.Object.hostInt pkt.len = true → Core.Object.hostInt pkt.bits.size = true →
    Pipe.extern_of_payload (Pipe.extern_to_yojson (.PacketIn pkt)) = .ok (.PacketIn pkt)

/-- `PacketStateText` as an evaluation rule: decoding the text of any JSON tree that is the
state of a packet within the host range yields that packet. The tree decoder identifies the
packet, and re-encoding it must give the same tree; both conditions are computed. -/
theorem packetStateText (h : PacketStateText) (json : Lean.Json) (pkt : Core.Object.PacketIn.t)
    (_ : Pipe.extern_of_yojson json = .ok (.PacketIn pkt))
    (henc : Pipe.extern_to_yojson (.PacketIn pkt) = json)
    (hidx : Core.Object.hostInt pkt.idx = true) (hlen : Core.Object.hostInt pkt.len = true)
    (hsize : Core.Object.hostInt pkt.bits.size = true) :
    Pipe.extern_of_payload json = .ok (.PacketIn pkt) :=
  henc ▸ h pkt hidx hlen hsize

end NanoP4Target
