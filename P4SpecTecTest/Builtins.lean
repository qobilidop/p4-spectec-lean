import P4SpecTec.Prelude

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

-- texts.ml
#guard Texts.strip_all_whitespace "a b  c" == "abc"
#guard Texts.strip_prefix "hello" "he" == some "llo"
#guard Texts.strip_prefix "hello" "x" == none
#guard Texts.strip_suffix "hello" "lo" == some "hel"
#guard Texts.split_text "a,b,,c" "," == some ["a", "b", "", "c"]
#guard Texts.split_text "a" ",," == none
#guard Texts.int_to_text (-3) == "-3"
#guard Texts.int_to_text 3 == "+3"
#guard Texts.text_to_int "-42" == some (-42)

-- lists.ml
#guard Lists.rev_ [1, 2, 3] == [3, 2, 1]
#guard Lists.concat_ [[1], [2, 3]] == [1, 2, 3]
#guard Lists.distinct_ ["a", "b"] == true
#guard Lists.distinct_ ["a", "a"] == false
#guard Lists.partition_ [1, 2, 3, 4] 1 == ([1], [2, 3, 4])
#guard Lists.assoc_ "b" [("a", 1), ("b", 2), ("b", 3)] == some 2
#guard Lists.assoc_ "z" [("a", 1)] == (none : Option Nat)
#guard Lists.sort_ [(2, "b"), (1, "a"), (2, "c")] == [(1, "a"), (2, "b"), (2, "c")]
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
#guard Maps.add_map [("a", 1), ("b", 2)] "a" 9 == [("a", 9), ("b", 2)]
#guard Maps.add_map [("a", 1)] "c" 3 == [("a", 1), ("c", 3)]
#guard Maps.find_map [("a", 1), ("a", 2)] "a" == some 1
#guard Maps.find_maps [[("a", 1)], [("b", 2)]] "b" == some 2
#guard Maps.adds_map [("a", 1)] ["b"] [2, 3] == none

-- nats.ml, ints.ml
#guard Nats.max_nat [] == none
#guard Nats.min_nat [3, 1] == some 1
#guard Ints.max_int [] == 0
#guard Ints.min_int [3, -1] == -1
