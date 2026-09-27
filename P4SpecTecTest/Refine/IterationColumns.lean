import P4SpecTec.Refine.IterationColumns

/-! Iteration columns preserve empty arity, order and independent projection encodings. -/

namespace P4SpecTecTest.Refine.IterationColumns

open P4SpecTec.Refine P4SpecTec.Lang.Il P4SpecTec.Prelude P4SpecTec.Interp_al

-- An empty batch still has both declared columns; ordinary transpose alone returns none.
example (left right : Unit → value) :
    ∃ columns,
      (pure (([left, right] : List (Unit → value)).map (fun _ => [])) :
        Eval (List (List value))) = pure columns ∧
      List.Forall₂ (fun column encode => canons column = canons (([] : List Unit).map encode))
        columns [left, right] :=
  transposeEncodedRows [left, right] .nil

-- Distinct field encoders, with arbitrary source metadata and no product ToValue instance.
theorem pairedColumns {α β : Type} (left : α → value) (right : β → value)
    (first : List value) (rest : List (List value)) (pairs : List (α × β))
    (related : List.Forall₂
      (fun row pair => canons row = canons [left pair.1, right pair.2])
      (first :: rest) pairs) :
    ∃ columns, Ctx.transpose (first :: rest) = (pure columns : Eval (List (List value))) ∧
      List.Forall₂ (fun column encode => canons column = canons (pairs.map encode))
        columns [fun pair => left pair.1, fun pair => right pair.2] :=
  transposeEncodedRows [fun pair : α × β => left pair.1, fun pair => right pair.2] related

/-- info: 'P4SpecTecTest.Refine.IterationColumns.pairedColumns' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairedColumns

-- Rectangularity is a real precondition: an unencoded ragged matrix still fails.
#guard match (Ctx.transpose [[], [P4SpecTec.Runtime.Value.Make.bool true]]).run with
  | some (.error .err) => true
  | _ => false

end P4SpecTecTest.Refine.IterationColumns
