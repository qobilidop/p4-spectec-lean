import P4SpecTec.Prelude.Value

/-!
Text builtins. Mirrors `p4spec/lib/interface/builtin/texts.ml`, function
for function, on byte strings (`ByteText`).
-/

namespace P4SpecTec.Builtin.Texts

/-- The value of an ASCII digit in `base`, if valid. -/
private def digit (base : Nat) (byte : UInt8) : Option Nat :=
  let n := byte.toNat
  let d :=
    if 48 ≤ n && n ≤ 57 then some (n - 48)
    else if 65 ≤ n && n ≤ 70 then some (n - 65 + 10)
    else if 97 ≤ n && n ≤ 102 then some (n - 97 + 10)
    else none
  d.filter (· < base)

/-- Zarith accepts underscores after the first digit, including repeated/trailing ones. -/
private def parse_digits (base : Nat) : List UInt8 → Bool → Nat → Option Nat
  | [], _, value => some value
  | byte :: rest, seen, value =>
    if byte == 95 then
      if seen then parse_digits base rest seen value else none
    else do
      let d ← digit base byte
      parse_digits base rest true (value * base + d)

/-- `dec $text_to_int(text) : int`; `none` where `Bigint.of_string` raises. -/
def text_to_int (s : ByteText) : Option Int := do
  let (negative, body) := match s.bytes.toList with
    | 45 :: rest => (true, rest)
    | 43 :: rest => (false, rest)
    | rest => (false, rest)
  let (base, digits) := match body with
    | 48 :: 120 :: rest => (16, rest)
    | 48 :: 88 :: rest => (16, rest)
    | 48 :: 111 :: rest => (8, rest)
    | 48 :: 79 :: rest => (8, rest)
    | 48 :: 98 :: rest => (2, rest)
    | 48 :: 66 :: rest => (2, rest)
    | rest => (10, rest)
  let magnitude ← parse_digits base digits false 0
  pure (if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude)

/-- `dec $int_to_text(int) : text` (`Num.string_of_num`, with a sign). -/
def int_to_text (i : Int) : ByteText :=
  ByteText.ofString ((if i ≥ 0 then "+" else "-") ++ toString i.natAbs)

/-- Split bytes on one separator byte, keeping leading, middle and trailing empty fields. -/
private def split_on_byte (sep : UInt8) : List UInt8 → List UInt8 → List (List UInt8)
  | [], current => [current.reverse]
  | byte :: rest, current =>
    if byte == sep then
      current.reverse :: split_on_byte sep rest []
    else
      split_on_byte sep rest (byte :: current)

/-- `dec $split_text(text, text) : text*`; the separator is one byte. -/
def split_text (s sep : ByteText) : Option (List ByteText) := do
  if sep.length != 1 then none
  else
    let byte ← sep.bytes.data[0]?
    pure ((split_on_byte byte s.bytes.toList []).map (ByteText.ofBytes ∘ List.toByteArray))

/-- `dec $strip_prefix(text, text) : text`. -/
def strip_prefix (s prefix_ : ByteText) : Option ByteText :=
  if prefix_.length ≤ s.length && s.bytes.extract 0 prefix_.length == prefix_.bytes then
    some ⟨s.bytes.extract prefix_.length s.length⟩
  else
    none

/-- `dec $strip_suffix(text, text) : text`. -/
def strip_suffix (s suffix : ByteText) : Option ByteText :=
  if suffix.length ≤ s.length &&
      s.bytes.extract (s.length - suffix.length) s.length == suffix.bytes then
    some ⟨s.bytes.extract 0 (s.length - suffix.length)⟩
  else
    none

/-- `dec $strip_all_whitespace(text) : text`: removes spaces. -/
def strip_all_whitespace (s : ByteText) : ByteText :=
  ⟨(s.bytes.toList.filter (· != 0x20)).toByteArray⟩

end P4SpecTec.Builtin.Texts
