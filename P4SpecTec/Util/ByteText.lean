import Init.Data.ByteArray.Basic
import Init.Data.String.Basic
import Init.Data.Ord.Array
import Init.Data.Order.Ord

/-!
Byte-oriented text for P4-SpecTec operations that can produce invalid UTF-8.
This is our own representation utility, not a mirror of an upstream module.

Unlike Lean `String`, this type preserves every byte sequence. Conversions to
`String` are explicit and decoding is checked. Indices and slice lengths count
bytes, not Unicode code points.
-/

namespace P4SpecTec

/-- Text represented by arbitrary bytes, including invalid UTF-8. -/
structure ByteText where
  /-- The exact byte sequence. -/
  bytes : ByteArray
  deriving DecidableEq

/-- Boolean equality decides exact byte equality. -/
instance : BEq ByteText where
  beq left right := decide (left = right)

/-- The Boolean equality test agrees with propositional equality. -/
instance : LawfulBEq ByteText where
  rfl := by intro text; exact of_decide_eq_self_eq_true _
  eq_of_beq := by intro left right h; exact of_decide_eq_true h

/-- Display the underlying byte values for diagnostics. -/
instance : Repr ByteText where
  reprPrec text _ := repr text.bytes.toList

namespace ByteText

/-- Wrap a byte array without checking UTF-8. -/
def ofBytes (bytes : ByteArray) : ByteText := ⟨bytes⟩

/-- Retrieve the exact bytes. -/
def toBytes (text : ByteText) : ByteArray := text.bytes

/-- Encode a Lean string as UTF-8 bytes. -/
def ofString (text : String) : ByteText := ⟨text.toUTF8⟩

/-- Decode only if the byte sequence is valid UTF-8. -/
def toString? (text : ByteText) : Option String := String.fromUTF8? text.bytes

/-- Number of bytes, not Unicode code points. -/
def length (text : ByteText) : Nat := text.bytes.size

/-- Concatenate exact byte sequences. -/
def append (left right : ByteText) : ByteText := ⟨left.bytes ++ right.bytes⟩

/-- Read one byte as a singleton byte text, if the index exists. -/
def idx (text : ByteText) (index : Nat) : Option ByteText :=
  if h : index < text.length then
    some ⟨ByteArray.empty.push (text.bytes.get index h)⟩
  else
    none

/-- Read a byte slice `[start, start + count)`, rejecting out-of-bounds requests. -/
def slice (text : ByteText) (start count : Nat) : Option ByteText :=
  if start ≤ text.length && count ≤ text.length - start then
    some ⟨text.bytes.extract start (start + count)⟩
  else
    none

/-- Replace one byte; the replacement must itself contain exactly one byte. -/
def setIdx (text : ByteText) (index : Nat) (replacement : ByteText) : Option ByteText := do
  if replacement.length != 1 then none
  else
    let byte ← replacement.bytes.data[0]?
    if h : index < text.length then
      some ⟨text.bytes.set index byte h⟩
    else
      none

/-- Replace exactly `count` bytes, keeping the total length unchanged. -/
def setSlice (text : ByteText) (start count : Nat)
    (replacement : ByteText) : Option ByteText := do
  if replacement.length != count then none
  else
    let before ← text.slice 0 start
    let suffix ← text.slice (start + count) (text.length - (start + count))
    some (before.append replacement |>.append suffix)

/-- Unsigned byte-lexicographic order, with a proper prefix ordered first. -/
def compare (left right : ByteText) : Ordering :=
  Array.compareLex (Ord.compare (α := UInt8)) left.bytes.data right.bytes.data

/-- Compare byte text in unsigned lexicographic order. -/
instance : Ord ByteText where
  compare := compare

/-- Byte-text equality is exactly equality of its stored bytes. -/
theorem eq_iff_bytes_eq (left right : ByteText) :
    left = right ↔ left.bytes = right.bytes := by
  constructor
  · intro h
    exact congrArg ByteText.bytes h
  · intro h
    cases left with
    | mk leftBytes =>
      cases right with
      | mk rightBytes =>
        exact congrArg ByteText.mk h

/-- info: 'P4SpecTec.ByteText.eq_iff_bytes_eq' does not depend on any axioms -/
#guard_msgs in #print axioms P4SpecTec.ByteText.eq_iff_bytes_eq

/-- Comparison reports equality exactly when the byte sequences are equal. -/
theorem compare_eq_iff_eq (left right : ByteText) :
    compare left right = .eq ↔ left = right := by
  constructor
  · intro h
    apply (eq_iff_bytes_eq left right).2
    apply ByteArray.ext
    exact Std.LawfulEqOrd.eq_of_compare (α := Array UInt8) h
  · intro h
    subst right
    change Array.compareLex (Ord.compare (α := UInt8)) left.bytes.data left.bytes.data = .eq
    exact Std.ReflCmp.compare_self

/-- info: 'P4SpecTec.ByteText.compare_eq_iff_eq' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms P4SpecTec.ByteText.compare_eq_iff_eq

/-- Lexicographic comparison reports equality only for identical bytes. -/
instance : Std.LawfulEqOrd ByteText where
  compare_self := (compare_eq_iff_eq _ _).2 rfl
  eq_of_compare := (compare_eq_iff_eq _ _).1

end ByteText
end P4SpecTec
