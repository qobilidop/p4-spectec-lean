import P4SpecTec.Lang.Il.Ast

/-!
Input hints of relations. Mirrors `p4spec/lib/lang/hints/input.ml`: the
positions of a relation's inputs among its arguments, and the split and
combination of argument lists by them. `init`, which reads an EL hint
expression, is not mirrored (the EL is not mirrored); `validate` is.
-/

namespace P4SpecTec.Lang.Hints.Input

open P4SpecTec.Util.Source

/-- Mirrors `t_phrase`. -/
abbrev t_phrase := List (phrase Int)

/-- Mirrors `to_string`. -/
def to_string (t : Lang.Il.Hints.Input.t) : String :=
  "hint(input " ++ " ".intercalate (t.map fun idx => "%" ++ toString idx) ++ ")"

/-- Mirrors `eq`. -/
def eq (a b : Lang.Il.Hints.Input.t) : Bool := a == b

/-- Mirrors `invalid`. -/
inductive invalid where
  /-- No input. -/
  | Empty
  /-- An index given twice, with both regions. -/
  | Duplicate_index (idx : Int) (first : region) (duplicate : region)
  /-- An index outside the arguments. -/
  | Out_of_bounds (idx : Int) («at» : region)

/-- Mirrors `validate`. -/
def validate (hint : t_phrase) (arity : Nat) : Except invalid Lang.Il.Hints.Input.t :=
  let rec find_duplicate (seen : List (phrase Int)) : List (phrase Int) → Option (Int × region × region)
    | [] => none
    | idx :: idxs =>
      match seen.find? fun s => s.it == idx.it with
      | some first => some (idx.it, first.at, idx.at)
      | none => find_duplicate (idx :: seen) idxs
  match hint with
  | [] => throw .Empty
  | _ =>
    match find_duplicate [] hint with
    | some (idx, at_first, at_duplicate) => throw (.Duplicate_index idx at_first at_duplicate)
    | none =>
      match hint.find? fun idx => idx.it < 0 || idx.it ≥ (arity : Int) with
      | some idx => throw (.Out_of_bounds idx.it idx.at)
      | none => pure (hint.map (·.it))

/-- Mirrors `split`: the items at input positions and the others. -/
def split {α : Type} (hint : Lang.Il.Hints.Input.t) (items : List α) : List α × List α :=
  let indexed := items.zipIdx
  (indexed.filterMap fun (x, i) => if hint.contains (Int.ofNat i) then some x else none,
   indexed.filterMap fun (x, i) => if hint.contains (Int.ofNat i) then none else some x)

/-- Mirrors `combine`: inputs and outputs back in argument order. -/
def combine {α : Type} (hint : Lang.Il.Hints.Input.t) (items_input items_output : List α) :
    List α :=
  let len := items_input.length + items_output.length
  let (idxs_input, idxs_output) :=
    (List.range len).partition fun i => hint.contains (Int.ofNat i)
  let indexed := idxs_input.zip items_input ++ idxs_output.zip items_output
  (indexed.mergeSort fun a b => a.1 ≤ b.1).map (·.2)

/-- Mirrors `is_conditional`: no outputs. -/
def is_conditional {α : Type} (hint : Lang.Il.Hints.Input.t) (items : List α) : Bool :=
  (split hint items).2.isEmpty

end P4SpecTec.Lang.Hints.Input
