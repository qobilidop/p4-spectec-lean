import P4SpecTec.Refine.Builtin.List

/-!
Numeric builtin contracts for all represented inputs, including boundary failures.
Numeric tags are preserved by `Rel`; a source-domain or call invariant must justify
that an actual source input has the declared representation before using these facts.
-/

namespace P4SpecTec.Refine.Builtin.Numeric

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine

/-- Related integer values decode to the exact integer, with arbitrary metadata. -/
theorem intDecodeOfRel {v : Lang.Il.value} {i : Int} (h : Rel v i) :
    P4SpecTec.Builtin.Call.int_of_value v = some i := by
  have hp := canon'_eq_num (canon_eq_it h)
  cases v with
  | mk payload note region =>
    change payload = .NumV (.Int i) at hp
    subst payload
    rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.intDecodeOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intDecodeOfRel

/-- A represented natural is converted to an integer exactly by the numeric dispatcher. -/
theorem natDecodeOfRel {v : Lang.Il.value} {n : Nat} (h : Rel v n) :
    P4SpecTec.Builtin.Call.int_of_value v = some (Int.ofNat n) := by
  have hp := canon'_eq_num (canon_eq_it h)
  cases v with
  | mk payload note region =>
    change payload = .NumV (.Nat n) at hp
    subst payload
    rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.natDecodeOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms natDecodeOfRel

/-- Signed interpretation agrees for every width and payload, including rejected widths. -/
theorem bitstrToIntRun {v w : Lang.Il.value} {width bits : Int}
    (hv : Rel v width) (hw : Rel w bits) (hints : P4.Unparse.HEnv) :
    (Interp_al.Effects.builtinEval hints "bitstr_to_int" [] [v, w]).run =
      (Eval.unmatch? (P4SpecTec.Builtin.Numerics.bitstr_to_int width bits)).run.map
        (Except.map toValue) := by
  have dispatch : P4SpecTec.Builtin.Call.invoke "bitstr_to_int" [] [v, w] = (do
      let x ← P4SpecTec.Builtin.Call.int_of_value v
      let y ← P4SpecTec.Builtin.Call.int_of_value w
      pure (Runtime.Value.Make.int (← P4SpecTec.Builtin.Numerics.bitstr_to_int x y))) := rfl
  have hintsDispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "bitstr_to_int" [] [v, w] =
      .ok (P4SpecTec.Builtin.Call.invoke "bitstr_to_int" [] [v, w]) := rfl
  rw [intDecodeOfRel hv, intDecodeOfRel hw] at dispatch
  change P4SpecTec.Builtin.Call.invoke "bitstr_to_int" [] [v, w] =
    (P4SpecTec.Builtin.Numerics.bitstr_to_int width bits).bind
      (fun i => some (Runtime.Value.Make.int i)) at dispatch
  simp only [Interp_al.Effects.builtinEval, hintsDispatch, dispatch]
  cases P4SpecTec.Builtin.Numerics.bitstr_to_int width bits <;> rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.bitstrToIntRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bitstrToIntRun

/-- Unsigned interpretation agrees at every width, including rejected widths. -/
theorem intToBitstrRun {v : Lang.Il.value} {x : Int} {w : Lang.Il.value} {y : Int}
    (hv : Rel v x) (hw : Rel w y) (hints : P4.Unparse.HEnv) :
    (Interp_al.Effects.builtinEval hints "int_to_bitstr" [] [v, w]).run =
      (Eval.unmatch? (P4SpecTec.Builtin.Numerics.int_to_bitstr x y)).run.map
        (Except.map toValue) := by
  have dispatch : P4SpecTec.Builtin.Call.invoke "int_to_bitstr" [] [v, w] = (do
      let a ← P4SpecTec.Builtin.Call.int_of_value v
      let b ← P4SpecTec.Builtin.Call.int_of_value w
      pure (Runtime.Value.Make.int (← P4SpecTec.Builtin.Numerics.int_to_bitstr a b))) := rfl
  have hintsDispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "int_to_bitstr" [] [v, w] =
      .ok (P4SpecTec.Builtin.Call.invoke "int_to_bitstr" [] [v, w]) := rfl
  rw [intDecodeOfRel hv, intDecodeOfRel hw] at dispatch
  change P4SpecTec.Builtin.Call.invoke "int_to_bitstr" [] [v, w] =
    (P4SpecTec.Builtin.Numerics.int_to_bitstr x y).bind
      (fun i => some (Runtime.Value.Make.int i)) at dispatch
  simp only [Interp_al.Effects.builtinEval, hintsDispatch, dispatch]
  cases P4SpecTec.Builtin.Numerics.int_to_bitstr x y <;> rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.intToBitstrRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intToBitstrRun

/-- Powers of two preserve exact natural-to-integer conversion. -/
theorem pow2Run {v : Lang.Il.value} {x : Nat}
    (hv : Rel v x) (hints : P4.Unparse.HEnv) :
    (Interp_al.Effects.builtinEval hints "pow2" [] [v]).run =
      (pure (P4SpecTec.Builtin.Numerics.pow2 (Int.ofNat x)) : Eval Int).run.map
        (Except.map toValue) := by
  have dispatch : P4SpecTec.Builtin.Call.invoke "pow2" [] [v] = (do
      let a ← P4SpecTec.Builtin.Call.int_of_value v
      pure (Runtime.Value.Make.int (P4SpecTec.Builtin.Numerics.pow2 a))) := rfl
  have hintsDispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "pow2" [] [v] =
      .ok (P4SpecTec.Builtin.Call.invoke "pow2" [] [v]) := rfl
  rw [natDecodeOfRel hv] at dispatch
  change P4SpecTec.Builtin.Call.invoke "pow2" [] [v] =
    some (Runtime.Value.Make.int (P4SpecTec.Builtin.Numerics.pow2 (Int.ofNat x))) at dispatch
  simp only [Interp_al.Effects.builtinEval, hintsDispatch, dispatch]
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.pow2Run' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pow2Run

/-- Bitwise negation preserves every represented integer. -/
theorem bnegRun {v : Lang.Il.value} {x : Int}
    (hv : Rel v x) (hints : P4.Unparse.HEnv) :
    (Interp_al.Effects.builtinEval hints "bneg" [] [v]).run =
      (pure (P4SpecTec.Builtin.Numerics.bneg x) : Eval Int).run.map (Except.map toValue) := by
  have dispatch : P4SpecTec.Builtin.Call.invoke "bneg" [] [v] = (do
      let a ← P4SpecTec.Builtin.Call.int_of_value v
      pure (Runtime.Value.Make.int (P4SpecTec.Builtin.Numerics.bneg a))) := rfl
  have hintsDispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "bneg" [] [v] =
      .ok (P4SpecTec.Builtin.Call.invoke "bneg" [] [v]) := rfl
  rw [intDecodeOfRel hv] at dispatch
  change P4SpecTec.Builtin.Call.invoke "bneg" [] [v] =
    some (Runtime.Value.Make.int (P4SpecTec.Builtin.Numerics.bneg x)) at dispatch
  simp only [Interp_al.Effects.builtinEval, hintsDispatch, dispatch]
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.bnegRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bnegRun

/-- Bitwise conjunction preserves arbitrary signed integers. -/
theorem bandRun {v : Lang.Il.value} {x : Int} {w : Lang.Il.value} {y : Int}
    (hv : Rel v x) (hw : Rel w y) (hints : P4.Unparse.HEnv) :
    (Interp_al.Effects.builtinEval hints "band" [] [v, w]).run =
      (pure (P4SpecTec.Builtin.Numerics.band x y) : Eval Int).run.map (Except.map toValue) := by
  have dispatch : P4SpecTec.Builtin.Call.invoke "band" [] [v, w] = (do
      let a ← P4SpecTec.Builtin.Call.int_of_value v
      let b ← P4SpecTec.Builtin.Call.int_of_value w
      pure (Runtime.Value.Make.int (P4SpecTec.Builtin.Numerics.band a b))) := rfl
  have hintsDispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "band" [] [v, w] =
      .ok (P4SpecTec.Builtin.Call.invoke "band" [] [v, w]) := rfl
  rw [intDecodeOfRel hv, intDecodeOfRel hw] at dispatch
  change P4SpecTec.Builtin.Call.invoke "band" [] [v, w] =
    some (Runtime.Value.Make.int (P4SpecTec.Builtin.Numerics.band x y)) at dispatch
  simp only [Interp_al.Effects.builtinEval, hintsDispatch, dispatch]
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.bandRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bandRun

/-- Bitwise exclusive disjunction preserves arbitrary signed integers. -/
theorem bxorRun {v : Lang.Il.value} {x : Int} {w : Lang.Il.value} {y : Int}
    (hv : Rel v x) (hw : Rel w y) (hints : P4.Unparse.HEnv) :
    (Interp_al.Effects.builtinEval hints "bxor" [] [v, w]).run =
      (pure (P4SpecTec.Builtin.Numerics.bxor x y) : Eval Int).run.map (Except.map toValue) := by
  have dispatch : P4SpecTec.Builtin.Call.invoke "bxor" [] [v, w] = (do
      let a ← P4SpecTec.Builtin.Call.int_of_value v
      let b ← P4SpecTec.Builtin.Call.int_of_value w
      pure (Runtime.Value.Make.int (P4SpecTec.Builtin.Numerics.bxor a b))) := rfl
  have hintsDispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "bxor" [] [v, w] =
      .ok (P4SpecTec.Builtin.Call.invoke "bxor" [] [v, w]) := rfl
  rw [intDecodeOfRel hv, intDecodeOfRel hw] at dispatch
  change P4SpecTec.Builtin.Call.invoke "bxor" [] [v, w] =
    some (Runtime.Value.Make.int (P4SpecTec.Builtin.Numerics.bxor x y)) at dispatch
  simp only [Interp_al.Effects.builtinEval, hintsDispatch, dispatch]
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.bxorRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bxorRun

/-- Bitwise disjunction preserves arbitrary signed integers. -/
theorem borRun {v : Lang.Il.value} {x : Int} {w : Lang.Il.value} {y : Int}
    (hv : Rel v x) (hw : Rel w y) (hints : P4.Unparse.HEnv) :
    (Interp_al.Effects.builtinEval hints "bor" [] [v, w]).run =
      (pure (P4SpecTec.Builtin.Numerics.bor x y) : Eval Int).run.map (Except.map toValue) := by
  have dispatch : P4SpecTec.Builtin.Call.invoke "bor" [] [v, w] = (do
      let a ← P4SpecTec.Builtin.Call.int_of_value v
      let b ← P4SpecTec.Builtin.Call.int_of_value w
      pure (Runtime.Value.Make.int (P4SpecTec.Builtin.Numerics.bor a b))) := rfl
  have hintsDispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "bor" [] [v, w] =
      .ok (P4SpecTec.Builtin.Call.invoke "bor" [] [v, w]) := rfl
  rw [intDecodeOfRel hv, intDecodeOfRel hw] at dispatch
  change P4SpecTec.Builtin.Call.invoke "bor" [] [v, w] =
    some (Runtime.Value.Make.int (P4SpecTec.Builtin.Numerics.bor x y)) at dispatch
  simp only [Interp_al.Effects.builtinEval, hintsDispatch, dispatch]
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.borRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms borRun

/-- Related Boolean inputs retain their exact bits when decoded by the raw dispatcher. -/
theorem boolDecodeOfRel {v : Lang.Il.value} {b : Bool} (h : Rel v b) :
    Runtime.Value.Get.bool v = some b := by
  have hp := canon'_eq_bool (canon_eq_it h)
  cases v with
  | mk payload note region =>
    change payload = .BoolV b at hp
    subst payload
    rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.boolDecodeOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boolDecodeOfRel

/-- Bit arrays decode at every length, preserving order and arbitrary element metadata. -/
theorem bitsDecodeOfRel {v : Lang.Il.value} {bits : List Bool} (h : Rel v bits) :
    P4SpecTec.Builtin.Call.bits_of_value v = some bits := by
  obtain ⟨vs, hv, hs⟩ := Builtin.List.listPayloadOfRel h
  have decoded : vs.mapM Runtime.Value.Get.bool = some bits := by
    clear h hv
    induction bits generalizing vs with
    | nil =>
      have hn := canons_eq_nil hs
      subst vs
      rfl
    | cons b bits ih =>
      obtain ⟨w, ws, rfl, hw, ht⟩ := canons_eq_cons hs
      simp only [List.mapM_cons, boolDecodeOfRel hw, ih ws ht]
      rfl
  cases v with
  | mk payload note region =>
    change payload = .ListV vs at hv
    subst payload
    exact decoded

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.bitsDecodeOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bitsDecodeOfRel

/-- Unsigned bit interpretation preserves every input, including the empty array. -/
theorem bitsToIntUnsignedRun {v : Lang.Il.value} {bits : List Bool}
    (hv : Rel v bits) (hints : P4.Unparse.HEnv) :
    (Interp_al.Effects.builtinEval hints "bits_to_int_unsigned" [] [v]).run =
      (pure (P4SpecTec.Builtin.Numerics.bits_to_int_unsigned bits) : Eval Int).run.map
        (Except.map toValue) := by
  have dispatch : P4SpecTec.Builtin.Call.invoke "bits_to_int_unsigned" [] [v] = (do
      let bs ← P4SpecTec.Builtin.Call.bits_of_value v
      pure (Runtime.Value.Make.int (P4SpecTec.Builtin.Numerics.bits_to_int_unsigned bs))) := rfl
  have hintsDispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "bits_to_int_unsigned" [] [v] =
      .ok (P4SpecTec.Builtin.Call.invoke "bits_to_int_unsigned" [] [v]) := rfl
  rw [bitsDecodeOfRel hv] at dispatch
  change P4SpecTec.Builtin.Call.invoke "bits_to_int_unsigned" [] [v] =
    some (Runtime.Value.Make.int (P4SpecTec.Builtin.Numerics.bits_to_int_unsigned bits)) at dispatch
  simp only [Interp_al.Effects.builtinEval, hintsDispatch, dispatch]
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.bitsToIntUnsignedRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bitsToIntUnsignedRun

/-- Signed bit interpretation preserves every input, including the empty array. -/
theorem bitsToIntSignedRun {v : Lang.Il.value} {bits : List Bool}
    (hv : Rel v bits) (hints : P4.Unparse.HEnv) :
    (Interp_al.Effects.builtinEval hints "bits_to_int_signed" [] [v]).run =
      (Eval.unmatch? (P4SpecTec.Builtin.Numerics.bits_to_int_signed bits)).run.map
        (Except.map toValue) := by
  have dispatch : P4SpecTec.Builtin.Call.invoke "bits_to_int_signed" [] [v] = (do
      let bs ← P4SpecTec.Builtin.Call.bits_of_value v
      pure (Runtime.Value.Make.int (← P4SpecTec.Builtin.Numerics.bits_to_int_signed bs))) := rfl
  have hintsDispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "bits_to_int_signed" [] [v] =
      .ok (P4SpecTec.Builtin.Call.invoke "bits_to_int_signed" [] [v]) := rfl
  rw [bitsDecodeOfRel hv] at dispatch
  change P4SpecTec.Builtin.Call.invoke "bits_to_int_signed" [] [v] =
    (P4SpecTec.Builtin.Numerics.bits_to_int_signed bits).bind
      (fun i => some (Runtime.Value.Make.int i)) at dispatch
  simp only [Interp_al.Effects.builtinEval, hintsDispatch, dispatch]
  cases P4SpecTec.Builtin.Numerics.bits_to_int_signed bits <;> rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.bitsToIntSignedRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bitsToIntSignedRun

/-- Unsigned bit output agrees canonically at every width, preserving width failures. -/
theorem intToBitsUnsignedRun {v w : Lang.Il.value} {width : Nat} {i : Int}
    (hv : Rel v width) (hw : Rel w i) (hints : P4.Unparse.HEnv) :
    ((Interp_al.Effects.builtinEval hints "int_to_bits_unsigned" [] [v, w]).run.map
      (Except.map canon)) =
      (Eval.unmatch? (P4SpecTec.Builtin.Numerics.int_to_bits_unsigned (Int.ofNat width) i)).run.map
        (Except.map (fun bits => canon (toValue bits))) := by
  have dispatch : P4SpecTec.Builtin.Call.invoke "int_to_bits_unsigned" [] [v, w] = (do
      let a ← P4SpecTec.Builtin.Call.int_of_value v
      let b ← P4SpecTec.Builtin.Call.int_of_value w
      pure (P4SpecTec.Builtin.Call.value_of_bits
        (← P4SpecTec.Builtin.Numerics.int_to_bits_unsigned a b))) := rfl
  have hintsDispatch :
      P4SpecTec.Builtin.Call.invokeWithHints hints "int_to_bits_unsigned" [] [v, w] =
      .ok (P4SpecTec.Builtin.Call.invoke "int_to_bits_unsigned" [] [v, w]) := rfl
  rw [natDecodeOfRel hv, intDecodeOfRel hw] at dispatch
  change P4SpecTec.Builtin.Call.invoke "int_to_bits_unsigned" [] [v, w] =
    (P4SpecTec.Builtin.Numerics.int_to_bits_unsigned (Int.ofNat width) i).bind
      (fun bits => some (P4SpecTec.Builtin.Call.value_of_bits bits)) at dispatch
  simp only [Interp_al.Effects.builtinEval, hintsDispatch, dispatch]
  cases P4SpecTec.Builtin.Numerics.int_to_bits_unsigned (Int.ofNat width) i <;> rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.intToBitsUnsignedRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intToBitsUnsignedRun

/-- Signed bit output agrees canonically at every width, preserving width failures. -/
theorem intToBitsSignedRun {v w : Lang.Il.value} {width : Nat} {i : Int}
    (hv : Rel v width) (hw : Rel w i) (hints : P4.Unparse.HEnv) :
    ((Interp_al.Effects.builtinEval hints "int_to_bits_signed" [] [v, w]).run.map
      (Except.map canon)) =
      (Eval.unmatch? (P4SpecTec.Builtin.Numerics.int_to_bits_signed (Int.ofNat width) i)).run.map
        (Except.map (fun bits => canon (toValue bits))) := by
  have dispatch : P4SpecTec.Builtin.Call.invoke "int_to_bits_signed" [] [v, w] = (do
      let a ← P4SpecTec.Builtin.Call.int_of_value v
      let b ← P4SpecTec.Builtin.Call.int_of_value w
      pure (P4SpecTec.Builtin.Call.value_of_bits
        (← P4SpecTec.Builtin.Numerics.int_to_bits_signed a b))) := rfl
  have hintsDispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "int_to_bits_signed" [] [v, w] =
      .ok (P4SpecTec.Builtin.Call.invoke "int_to_bits_signed" [] [v, w]) := rfl
  rw [natDecodeOfRel hv, intDecodeOfRel hw] at dispatch
  change P4SpecTec.Builtin.Call.invoke "int_to_bits_signed" [] [v, w] =
    (P4SpecTec.Builtin.Numerics.int_to_bits_signed (Int.ofNat width) i).bind
      (fun bits => some (P4SpecTec.Builtin.Call.value_of_bits bits)) at dispatch
  simp only [Interp_al.Effects.builtinEval, hintsDispatch, dispatch]
  cases P4SpecTec.Builtin.Numerics.int_to_bits_signed (Int.ofNat width) i <;> rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.intToBitsSignedRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intToBitsSignedRun

/-- Every Nano numeric operation rejects incorrect value arity before decoding.
The legacy numeric dispatcher ignores type arguments, so none are rejected here. -/
theorem numericArity (name : String) (arity : Nat)
    (operation : (name, arity) ∈ [("bitstr_to_int", 2),
        ("int_to_bitstr", 2),
        ("pow2", 1),
        ("bneg", 1),
        ("band", 2),
        ("bxor", 2),
        ("bor", 2),
        ("bits_to_int_unsigned", 1),
        ("bits_to_int_signed", 1),
        ("int_to_bits_unsigned", 2),
        ("int_to_bits_signed", 2)])
    (hints : P4.Unparse.HEnv) (types : List Lang.Il.typ) (args : List Lang.Il.value)
    (wrong : args.length ≠ arity) :
    (Interp_al.Effects.builtinEval hints name types args).run = some (.error .unmatch) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at operation
  rcases operation with ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
  all_goals
    cases args with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => first | exact False.elim (wrong rfl) | rfl
      | cons b rest =>
        cases rest with
        | nil => first | exact False.elim (wrong rfl) | rfl
        | cons c rest => rfl

/-- info: 'P4SpecTec.Refine.Builtin.Numeric.numericArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms numericArity

end P4SpecTec.Refine.Builtin.Numeric
