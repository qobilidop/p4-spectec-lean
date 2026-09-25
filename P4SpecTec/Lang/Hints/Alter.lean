import P4SpecTec.Domain.Atom
import P4SpecTec.Util.Source
import Lean.Data.Json.Printer

/-!
Alternation hints. Mirrors `p4spec/lib/lang/hints/alter.ml` at the pinned
upstream commit: constructor order, validation cursor, and alternation
traversal. The EL expression language is not ported, so `OtherH` retains
raw JSON and fails closed during rendering. Its decoder lives in
`AlterJson.lean` and rejects unsupported EL forms.
-/

namespace P4SpecTec.Lang.Hints.Alter

open P4SpecTec.Util.Source
open P4SpecTec.Domain

/-- A placeholder, corresponding to upstream's polymorphic variant. -/
inductive hole where
  /-- The next argument at the current cursor. -/
  | Next
  /-- An explicit argument index. -/
  | Num (idx : Int)
  deriving BEq

/-- Mirrors `t`; `OtherH` holds EL JSON until that language is ported. -/
inductive t where
  /-- Literal text. -/
  | TextH (text : String)
  /-- An atom with its source location. -/
  | AtomH (atom : phrase Atom.t)
  /-- Space-separated elements. -/
  | SeqH (hints : List t)
  /-- Two atoms around a nested hint. -/
  | BrackH (left : phrase Atom.t) (hint : t) (right : phrase Atom.t)
  /-- An implicit or indexed placeholder. -/
  | HoleH (hole : phrase hole)
  /-- Concatenation without a separator. -/
  | FuseH (left right : t)
  /-- An EL expression outside the supported alteration subset. -/
  | OtherH (raw : Lean.Json)

mutual

/-- Mirrors `to_string` for supported forms; `OtherH` is diagnostic JSON. -/
def to_string (hint : t) : String := "hint(alter " ++ to_string' hint ++ ")"

/-- Mirrors `to_string'` for supported forms; `OtherH` is diagnostic JSON. -/
def to_string' : t → String
  | .TextH str => str
  | .AtomH atom => Atom.string_of_atom atom.it
  | .SeqH hints => " ".intercalate (to_string_list hints)
  | .BrackH left hint right =>
    Atom.string_of_atom left.it ++ " " ++ to_string' hint ++ " " ++
      Atom.string_of_atom right.it
  | .HoleH ⟨.Next, _, _⟩ => "%"
  | .HoleH ⟨.Num idx, _, _⟩ => "%" ++ toString idx
  | .FuseH left right => to_string' left ++ "#" ++ to_string' right
  | .OtherH raw => raw.compress

/-- The list traversal for `SeqH`, so recursion stays structural. -/
def to_string_list : List t → List String
  | [] => []
  | hint :: hints => to_string' hint :: to_string_list hints

end

/-- Mirrors `invalid_oob`. -/
structure invalid_oob where
  /-- The placeholder's location. -/
  «at» : region
  /-- The placeholder as written. -/
  placeholder : String
  /-- The requested argument position. -/
  index : Int
  /-- The number of available arguments. -/
  arity : Nat
  deriving BEq

mutual

/-- Mirrors `validate`. -/
def validate (hint : t) (arity : Nat) : Except invalid_oob Unit := do
  let _ ← validate' 0 hint arity
  pure ()

/-- Mirrors `validate'`: the cursor moves only for `Next`, left to right. -/
def validate' (cursor : Nat) (hint : t) (arity : Nat) :
    Except invalid_oob Nat := do
  match hint with
  | .TextH _ | .AtomH _ | .OtherH _ => pure cursor
  | .SeqH hints => validate_list cursor hints arity
  | .BrackH _ hint _ => validate' cursor hint arity
  | .HoleH ⟨.Next, _, loc⟩ =>
    if cursor < arity then pure (cursor + 1)
    else throw { «at» := loc, placeholder := "%", index := cursor, arity }
  | .HoleH ⟨.Num idx, _, loc⟩ =>
    if 0 ≤ idx && idx < arity then pure cursor
    else throw { «at» := loc, placeholder := "%" ++ toString idx, index := idx, arity }
  | .FuseH left right => do
    let cursor ← validate' cursor left arity
    validate' cursor right arity

/-- The left-to-right list traversal of `validate'`. -/
def validate_list (cursor : Nat) (hints : List t) (arity : Nat) :
    Except invalid_oob Nat := do
  match hints with
  | [] => pure cursor
  | hint :: hints =>
    let cursor ← validate' cursor hint arity
    validate_list cursor hints arity

end

mutual

/-- Structural policy equality, ignoring source regions. -/
def policyEq : t → t → Bool
  | .TextH a, .TextH b => a == b
  | .AtomH a, .AtomH b => Atom.eq a.it b.it
  | .SeqH as, .SeqH bs => policyEqList as bs
  | .BrackH la a ra, .BrackH lb b rb =>
    Atom.eq la.it lb.it && policyEq a b && Atom.eq ra.it rb.it
  | .HoleH a, .HoleH b => a.it == b.it
  | .FuseH la ra, .FuseH lb rb => policyEq la lb && policyEq ra rb
  | .OtherH a, .OtherH b => a == b
  | _, _ => false

/-- Elementwise alteration equality for sequences. -/
def policyEqList : List t → List t → Bool
  | [], [] => true
  | a :: as, b :: bs => policyEq a b && policyEqList as bs
  | _, _ => false

end

/-- Mirrors `alternate`. Missing items and unsupported `OtherH` return
errors instead of raising an OCaml exception. -/
def alternate {α δ : Type} (empty : δ) (text : String → Option δ)
    (atom : phrase Atom.t → δ) (join : List δ → δ) (fuse : δ → δ → δ)
    (hint : t) (render : α → δ) (items : List α) : Except String δ := do
  let (_, result) ← go hint 0
  pure (result.getD empty)
where
  /-- Traverse the hint with the current implicit-hole cursor. -/
  go (hint : t) (cursor : Nat) : Except String (Nat × Option δ) := do
    match hint with
    | .TextH str => pure (cursor, text str)
    | .AtomH a => pure (cursor, some (atom a))
    | .SeqH hints =>
      let (cursor, ds) ← goList hints cursor
      pure (cursor, some (join ds))
    | .BrackH left hint right =>
      let (cursor, d) ← go hint cursor
      pure (cursor, some (join ([atom left] ++ d.toList ++ [atom right])))
    | .HoleH ⟨.Next, _, _⟩ =>
      match items[cursor]? with
      | some item => pure (cursor + 1, some (render item))
      | none => throw s!"alteration hole %{cursor} exceeds {items.length} items"
    | .HoleH ⟨.Num idx, _, _⟩ =>
      if idx < 0 then throw s!"alteration hole %{idx} is negative"
      match items[idx.toNat]? with
      | some item => pure (cursor, some (render item))
      | none => throw s!"alteration hole %{idx} exceeds {items.length} items"
    | .FuseH left right =>
      let (cursor, dLeft) ← go left cursor
      let (cursor, dRight) ← go right cursor
      pure (cursor, some (fuse (dLeft.getD empty) (dRight.getD empty)))
    | .OtherH _ => throw "unsupported alteration hint expression"

  /-- Sequence traversal preserving the implicit-hole cursor. -/
  goList (hints : List t) (cursor : Nat) : Except String (Nat × List δ) := do
    match hints with
    | [] => pure (cursor, [])
    | hint :: hints =>
      let (cursor, d) ← go hint cursor
      let (cursor, ds) ← goList hints cursor
      pure (cursor, d.getD empty :: ds)

end P4SpecTec.Lang.Hints.Alter
