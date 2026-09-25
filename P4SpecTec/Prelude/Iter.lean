import P4SpecTec.Prelude.Value

/-!
Helpers for the generated code's indexing, slicing and iteration, with
the interpreter's failure conditions (`eval_idx_exp`, `eval_slice_exp`,
`Ctx.sub_list`): an index or slice out of bounds is `none`.
-/

namespace P4SpecTec.Prelude.Iter

/-- `xs[i]` for a natural index. -/
def idx {α : Type} (xs : List α) (i : Nat) : Option α := xs[i]?

/-- `xs[i]` for an integer index; negative is out of bounds. -/
def idxInt {α : Type} (xs : List α) (i : Int) : Option α :=
  if i < 0 then none else xs[i.toNat]?

/-- `s[i]` on a text: the one-byte text at `i`. -/
def idxText (s : ByteText) (i : Nat) : Option ByteText := s.idx i

/-- `xs[i : n]`: the `n` elements from `i`; `none` unless `i + n ≤ |xs|`. -/
def slice {α : Type} (xs : List α) (i n : Nat) : Option (List α) :=
  if i + n ≤ xs.length then some ((xs.drop i).take n) else none

/-- `s[i : n]` on a text. -/
def sliceText (s : ByteText) (i n : Nat) : Option ByteText := s.slice i n

/-- `xs[i = v]`: replace the element at `i`; `none` when out of bounds. -/
def setIdx {α : Type} (xs : List α) (i : Nat) (v : α) : Option (List α) :=
  if i < xs.length then some (xs.set i v) else none

/-- `xs[i : n = vs]`: replace the slice; `none` when out of bounds or
`vs` has another length. -/
def setSlice {α : Type} (xs : List α) (i n : Nat) (vs : List α) : Option (List α) :=
  if i + n ≤ xs.length && vs.length == n then some (xs.take i ++ vs ++ xs.drop (i + n)) else none

/-- Joint iteration over two lists of equal length, as `Ctx.sub_list`
requires; `none` on a length mismatch. -/
def zip2 {α β : Type} (xs : List α) (ys : List β) : Option (List (α × β)) :=
  if xs.length == ys.length then some (xs.zip ys) else none

end P4SpecTec.Prelude.Iter
