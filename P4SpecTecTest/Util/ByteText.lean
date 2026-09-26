import P4SpecTec.Util.ByteText

/-!
Byte-level regression tests: invalid UTF-8 remains representable across
indexing, replacement, slicing and concatenation.
-/

open P4SpecTec

private def accented := ByteText.ofString "é"
private def arbitrary := ByteText.ofBytes (ByteArray.mk #[0x00, 0xff])

#guard accented.length == 2
#guard accented.idx 0 == some (ByteText.ofBytes (ByteArray.mk #[0xc3]))
#guard (accented.idx 0 >>= ByteText.toString?) == none
#guard accented.toString? == some "é"
#guard accented.setIdx 0 (ByteText.ofString "X") ==
  some (ByteText.ofBytes (ByteArray.mk #[0x58, 0xa9]))
#guard (accented.setIdx 0 (ByteText.ofString "X") >>= ByteText.toString?) == none
#guard arbitrary.length == 2
#guard (ByteText.ofBytes arbitrary.toBytes) == arbitrary
#guard arbitrary.idx 0 == some (ByteText.ofBytes (ByteArray.mk #[0x00]))
#guard arbitrary.idx 1 == some (ByteText.ofBytes (ByteArray.mk #[0xff]))
#guard arbitrary.toString? == none
#guard accented.idx 2 == none
#guard accented.slice 0 0 == some (ByteText.ofBytes ByteArray.empty)
#guard accented.slice 2 0 == some (ByteText.ofBytes ByteArray.empty)
#guard accented.slice 2 1 == none
#guard accented.slice 3 0 == none
#guard accented.setIdx 2 (ByteText.ofString "X") == none
#guard accented.setIdx 0 (ByteText.ofString "") == none
#guard accented.setIdx 0 (ByteText.ofString "ab") == none
#guard accented.setSlice 0 1 (ByteText.ofString "X") ==
  some (ByteText.ofBytes (ByteArray.mk #[0x58, 0xa9]))
#guard accented.setSlice 0 2 (ByteText.ofString "X") == none
#guard accented.setSlice 2 0 (ByteText.ofString "") == some accented
#guard accented.setSlice 2 1 (ByteText.ofString "X") == none
#guard arbitrary.setSlice 0 1 (ByteText.ofString "X") ==
  some (ByteText.ofBytes (ByteArray.mk #[0x58, 0xff]))
#guard accented.append arbitrary ==
  ByteText.ofBytes (ByteArray.mk #[0xc3, 0xa9, 0x00, 0xff])
#guard ByteText.compare (ByteText.ofString "a") (ByteText.ofString "a") == .eq
#guard ByteText.compare (ByteText.ofString "a") (ByteText.ofString "aa") == .lt
#guard ByteText.compare (ByteText.ofString "b") (ByteText.ofString "aa") == .gt
#guard ByteText.compare (ByteText.ofBytes (ByteArray.mk #[0xff]))
  (ByteText.ofBytes (ByteArray.mk #[0x00])) == .gt

example : ByteText.ofString "a" = ByteText.ofString "a" := by decide

example : ByteText.compare (ByteText.ofString "a") (ByteText.ofString "a") = .eq :=
  (ByteText.compare_eq_iff_eq _ _).mpr rfl

example (left right : ByteText) : left == right ↔ left = right := beq_iff_eq
