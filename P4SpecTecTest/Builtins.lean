import P4SpecTec.Prelude
import P4SpecTec.Interface.Builtin.Call

/-!
Unit tests for the ports under `P4SpecTec/Interface/Builtin/` (design
section 5.2). Expected values were computed from the OCaml definitions in
`p4spec/lib/interface/builtin/*.ml` by hand or by transliterating them
into Python big-integer arithmetic; each `#guard` names the OCaml function.
-/

open P4SpecTec.Builtin

-- numerics.ml: bitstr_to_int' normalises into [-2^(w-1), 2^(w-1)) however far
-- the input is (65025 = 0xFE01 needs 4064 subtractions of 16 at width 4)
#guard Numerics.bitstr_to_int' 4 65025 == 1
#guard Numerics.bitstr_to_int' 4 8 == -8
#guard Numerics.bitstr_to_int' 4 7 == 7
#guard Numerics.bitstr_to_int' 4 (-9) == 7
#guard Numerics.bitstr_to_int' 8 200 == -56
#guard Numerics.bitstr_to_int' 0 5 == 0
-- int_to_bitstr' is the non-negative residue
#guard Numerics.int_to_bitstr' 4 (-1) == 15
#guard Numerics.int_to_bitstr' 4 17 == 1
#guard Numerics.int_to_bitstr' 8 (-256) == 0
-- pow2', shifts (truncating halving)
#guard Numerics.pow2 10 == 1024
#guard Numerics.shl 3 4 == some 48
#guard Numerics.shr (-7) 1 == some (-3)
#guard Numerics.shr 3 3000 == none
#guard Numerics.shr_arith (-7) 1 (-4) == some (-7)
-- two's-complement bitwise operations on negative integers (Bigint.bit_*)
#guard Numerics.band (-6) 3 == 2
#guard Numerics.bor (-6) 3 == -5
#guard Numerics.bxor (-6) 3 == -7
#guard Numerics.bneg 5 == -6
#guard Numerics.band 12 10 == 8
-- bit arrays, most significant bit first
#guard Numerics.bits_to_int_unsigned [true, false, true] == 5
#guard Numerics.bits_to_int_signed [true, false, true] == some (-3)
#guard Numerics.bits_to_int_signed [false, true, true] == some 3
#guard Numerics.bits_to_int_signed [] == none
#guard Numerics.int_to_bits_unsigned 4 5 == some [false, true, false, true]
#guard Numerics.int_to_bits_signed 4 (-3) == some [true, true, false, true]
-- bitacc n[m:l] and bitacc_replace
#guard Numerics.bitacc 0xF0 7 4 == some 15
#guard Numerics.bitacc 0xF0 3 0 == some 0
#guard Numerics.bitacc 1 1 (-1) == none
#guard Numerics.bitacc_replace 0xFF 7 4 0 == 0x0F
#guard Numerics.bitacc_replace 0 3 0 5 == 5

-- texts.ml: all positions and separators are bytes, even inside UTF-8 sequences.
private def bt := P4SpecTec.ByteText.ofString
private def raw := P4SpecTec.ByteText.ofBytes

-- Arity is retryable, but correctly applied bad payloads abort. These inputs
-- cannot be passed to typed generated wrappers, so exercise checked dispatch.
private def dispatch := Call.invokeWithHints []
private def isMismatch : Except String (Option P4SpecTec.Lang.Il.value) → Bool
  | .ok none => true
  | _ => false
private def isHard : Except String (Option P4SpecTec.Lang.Il.value) → Bool
  | .error _ => true
  | _ => false
#guard isMismatch (dispatch "text_to_int" [] [])
#guard isMismatch (dispatch "split_text" [] [P4SpecTec.Runtime.Value.Make.text (bt "a")])
#guard isMismatch (dispatch "int_to_text" [P4SpecTec.Util.Source.mkPhrase .TextT]
  [P4SpecTec.Runtime.Value.Make.int 1])
#guard isHard (dispatch "text_to_int" [] [P4SpecTec.Runtime.Value.Make.int 1])
#guard isHard (dispatch "int_to_text" [] [P4SpecTec.Runtime.Value.Make.text (bt "1")])
#guard isHard (dispatch "strip_prefix" []
  [P4SpecTec.Runtime.Value.Make.text (bt "a"), P4SpecTec.Runtime.Value.Make.int 1])

#guard Texts.strip_all_whitespace (bt "a b  c") == bt "abc"
#guard Texts.strip_all_whitespace (raw (ByteArray.mk #[0xff, 0x20, 0x09, 0x00])) ==
  raw (ByteArray.mk #[0xff, 0x09, 0x00])
#guard Texts.strip_prefix (bt "hello") (bt "he") == some (bt "llo")
#guard Texts.strip_prefix (bt "hello") (bt "x") == none
#guard Texts.strip_prefix (bt "é") (raw (ByteArray.mk #[0xc3])) ==
  some (raw (ByteArray.mk #[0xa9]))
#guard Texts.strip_suffix (bt "hello") (bt "lo") == some (bt "hel")
#guard Texts.strip_suffix (bt "é") (raw (ByteArray.mk #[0xa9])) ==
  some (raw (ByteArray.mk #[0xc3]))
#guard Texts.split_text (bt "a,b,,c") (bt ",") ==
  some [bt "a", bt "b", bt "", bt "c"]
#guard Texts.split_text (bt "é") (raw (ByteArray.mk #[0xc3])) ==
  some [bt "", raw (ByteArray.mk #[0xa9])]
#guard Texts.split_text (raw (ByteArray.mk #[0x00, 0xff, 0x00]))
  (raw (ByteArray.mk #[0x00])) == some [bt "", raw (ByteArray.mk #[0xff]), bt ""]
#guard Texts.split_text (bt "a") (bt ",,") == none
#guard Texts.split_text (bt "a") (bt "é") == none
#guard Texts.int_to_text (-3) == bt "-3"
#guard Texts.int_to_text 3 == bt "+3"
#guard Texts.text_to_int (bt "-42") == some (-42)
#guard Texts.text_to_int (bt "0xFF") == some 255
#guard Texts.text_to_int (bt "-0Xf") == some (-15)
#guard Texts.text_to_int (bt "+0b101") == some 5
#guard Texts.text_to_int (bt "0o77") == some 63
#guard Texts.text_to_int (bt "1__2_") == some 12
#guard Texts.text_to_int (bt "") == some 0
#guard Texts.text_to_int (bt "-") == some 0
#guard Texts.text_to_int (bt "0x") == some 0
#guard Texts.text_to_int (bt "123456789012345678901234567890") ==
  some 123456789012345678901234567890
#guard Texts.text_to_int (bt "_1") == none
#guard Texts.text_to_int (bt "0x_1") == none
#guard Texts.text_to_int (bt " 2") == none
#guard Texts.text_to_int (bt "é") == none
#guard Texts.text_to_int (raw (ByteArray.mk #[0xff])) == none

private def textValue := P4SpecTec.Runtime.Value.Make.text
private def getText := P4SpecTec.Runtime.Value.Get.text

#guard (Call.invoke "int_to_text" [] [P4SpecTec.Runtime.Value.Make.int 3] >>= getText) ==
  some (bt "+3")
#guard (Call.invoke "strip_prefix" []
    [textValue (bt "é"), textValue (raw (ByteArray.mk #[0xc3]))] >>= getText) ==
  some (raw (ByteArray.mk #[0xa9]))
#guard ((Call.invoke "split_text" []
    [textValue (bt "é"), textValue (raw (ByteArray.mk #[0xc3]))]).bind fun v => do
      (← P4SpecTec.Runtime.Value.Get.list v).mapM getText) ==
  some [bt "", raw (ByteArray.mk #[0xa9])]

-- lists.ml
#guard Lists.rev_ [1, 2, 3] == [3, 2, 1]
#guard Lists.concat_ [[1], [2, 3]] == [1, 2, 3]
#guard Lists.distinct_ [bt "a", bt "b"] == true
#guard Lists.distinct_ [bt "a", bt "a"] == false
#guard Lists.partition_ [1, 2, 3, 4] 1 == ([1], [2, 3, 4])
#guard Lists.assoc_ (bt "b") [(bt "a", 1), (bt "b", 2), (bt "b", 3)] == some 2
#guard Lists.assoc_ (bt "z") [(bt "a", 1)] == (none : Option Nat)
#guard Lists.sort_ [(2, bt "b"), (1, bt "a"), (2, bt "c")] ==
  [(1, bt "a"), (2, bt "b"), (2, bt "c")]
#guard Lists.transpose_ [[1, 2], [3, 4]] == some [[1, 3], [2, 4]]
#guard Lists.transpose_ [[1, 2], [3]] == none

-- sets.ml: results in Value.compare order, deduplicated
#guard Sets.union_set [3, 1] [2, 1] == [1, 2, 3]
#guard Sets.intersect_set [3, 1, 2] [2, 3] == [2, 3]
#guard Sets.diff_set [3, 1, 2] [2] == [1, 3]
#guard Sets.unions_set [[2], [1], [2]] == [1, 2]
#guard Sets.sub_set [1] [2, 1] == true
#guard Sets.eq_set [1, 2] [2, 1] == true

-- maps.ml: update in place, else append; find first
#guard Maps.add_map [(bt "a", 1), (bt "b", 2)] (bt "a") 9 ==
  [(bt "a", 9), (bt "b", 2)]
#guard Maps.add_map [(bt "a", 1)] (bt "c") 3 == [(bt "a", 1), (bt "c", 3)]
#guard Maps.find_map [(bt "a", 1), (bt "a", 2)] (bt "a") == some 1
#guard Maps.find_maps [[(bt "a", 1)], [(bt "b", 2)]] (bt "b") == some 2
#guard Maps.adds_map [(bt "a", 1)] [bt "b"] [2, 3] == none

-- nats.ml, ints.ml
#guard Nats.max_nat [] == none
#guard Nats.min_nat [3, 1] == some 1
#guard Ints.max_int [] == 0
#guard Ints.min_int [3, -1] == -1
