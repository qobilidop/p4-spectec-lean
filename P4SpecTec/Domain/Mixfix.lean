import P4SpecTec.Util.Source
import P4SpecTec.Domain.Atom

/-!
Mixfix notation: a tree of atoms around argument holes. Mirrors
`p4spec/lib/domain/mixfix.ml` (the type and the functions the compiler
uses) and `mixop.ml`.
-/

namespace P4SpecTec.Domain.Mixfix

open P4SpecTec.Util.Source

/-- Mirrors `Mixfix.atom`: an atom with its source region. -/
abbrev atom := phrase Atom.t

/-- Mirrors `'a Mixfix.t`. -/
inductive t (α : Type) where
  /-- An argument hole, filled with `α`. -/
  | Arg (a : α)
  /-- A bare atom. -/
  | Atom (a : atom)
  /-- Brackets around a mixfix. -/
  | Brack (l : atom) (m : t α) (r : atom)
  /-- An infix atom between two mixfixes. -/
  | Infix (l : t α) (a : atom) (r : t α)
  /-- A sequence. -/
  | Seq (ms : List (t α))
  deriving Repr, Inhabited

/-- Mirrors `Mixfix.mixop`: a mixfix with unit holes. -/
abbrev mixop := t Unit

/-- Mirrors `Mixfix.map`. -/
def map {α β : Type} (f : α → β) : t α → t β
  | .Arg a => .Arg (f a)
  | .Atom a => .Atom a
  | .Brack l m r => .Brack l (map f m) r
  | .Infix l a r => .Infix (map f l) a (map f r)
  | .Seq ms => .Seq (ms.map (map f))

/-- Mirrors `Mixfix.to_mixop`. -/
def to_mixop {α : Type} (m : t α) : mixop := map (fun _ => ()) m

/-- Mirrors `Mixfix.args`: the holes' contents, left to right. -/
def args {α : Type} : t α → List α
  | .Arg a => [a]
  | .Atom _ => []
  | .Brack _ m _ => args m
  | .Infix l _ r => args l ++ args r
  | .Seq ms => ms.flatMap args

/-- Mirrors `Mixfix.atoms`: the atoms, left to right. -/
def atoms {α : Type} : t α → List atom
  | .Arg _ => []
  | .Atom a => [a]
  | .Brack l m r => l :: atoms m ++ [r]
  | .Infix l a r => atoms l ++ [a] ++ atoms r
  | .Seq ms => ms.flatMap atoms

/-- Mirrors `Mixfix.arity`. -/
def arity {α : Type} (m : t α) : Nat := (args m).length

/-- Mirrors `Mixfix.eq`, given equality on the holes. -/
def eq {α β : Type} (eq_arg : α → β → Bool) : t α → t β → Bool
  | .Arg a, .Arg b => eq_arg a b
  | .Atom a, .Atom b => Atom.eq a.it b.it
  | .Brack la ma ra, .Brack lb mb rb =>
    Atom.eq la.it lb.it && eq eq_arg ma mb && Atom.eq ra.it rb.it
  | .Infix la aa ra, .Infix lb ab rb =>
    Atom.eq aa.it ab.it && eq eq_arg la lb && eq eq_arg ra rb
  | .Seq as, .Seq bs => eqs eq_arg as bs
  | _, _ => false
where
  /-- Mirrors `Mixfix.eqs`. -/
  eqs {α β : Type} (eq_arg : α → β → Bool) : List (t α) → List (t β) → Bool
    | [], [] => true
    | a :: as, b :: bs => eq eq_arg a b && eqs eq_arg as bs
    | _, _ => false

/-- Mirrors `Mixfix.eq_mixop`: equality ignoring the holes. -/
def eq_mixop {α β : Type} (a : t α) (b : t β) : Bool := eq (fun _ _ => true) a b

/-- The constructor's position, for `compare`. -/
def tag {α : Type} : t α → Nat
  | .Arg _ => 0 | .Atom _ => 1 | .Brack .. => 2 | .Infix .. => 3 | .Seq _ => 4

/-- Mirrors `Mixfix.compare`, given a comparison on the holes. The OCaml
short-circuits on physical equality, which changes nothing observable. -/
def compare {α β : Type} (compare_arg : α → β → Ordering) : t α → t β → Ordering
  | .Arg a, .Arg b => compare_arg a b
  | .Atom a, .Atom b => Atom.compare a.it b.it
  | .Brack la ma ra, .Brack lb mb rb =>
    (Atom.compare la.it lb.it).then ((compare compare_arg ma mb).then (Atom.compare ra.it rb.it))
  | .Infix la aa ra, .Infix lb ab rb =>
    (compare compare_arg la lb).then ((Atom.compare aa.it ab.it).then (compare compare_arg ra rb))
  | .Seq as, .Seq bs => compares compare_arg as bs
  | a, b => Ord.compare (tag a) (tag b)
where
  /-- The inner `compare_mixfixes`. -/
  compares {α β : Type} (compare_arg : α → β → Ordering) : List (t α) → List (t β) → Ordering
    | [], [] => .eq
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
    | a :: as, b :: bs => (compare compare_arg a b).then (compares compare_arg as bs)

/-- Mirrors `Mixfix.compare_mixop`. -/
def compare_mixop {α β : Type} (a : t α) (b : t β) : Ordering :=
  compare (fun _ _ => .eq) a b

/-- Mirrors `Mixfix.fill`: put arguments into the holes, left to right.
`none` on an arity mismatch, where the OCaml raises `Arity_mismatch`. -/
def fill {α : Type} (m : mixop) (as : List α) : Option (t α) :=
  match go m as with
  | some (m', []) => some m'
  | _ => none
where
  /-- The inner `fill'`. -/
  go : mixop → List α → Option (t α × List α)
    | .Arg (), a :: as => some (.Arg a, as)
    | .Arg (), [] => none
    | .Atom a, as => some (.Atom a, as)
    | .Brack l m r, as => do let (m', as) ← go m as; pure (.Brack l m' r, as)
    | .Infix l a r, as => do
      let (l', as) ← go l as
      let (r', as) ← go r as
      pure (.Infix l' a r', as)
    | .Seq ms, as => do let (ms', as) ← goSeq ms as; pure (.Seq ms', as)
  /-- `fill'` over a sequence. -/
  goSeq : List mixop → List α → Option (List (t α) × List α)
    | [], as => some ([], as)
    | m :: ms, as => do
      let (m', as) ← go m as
      let (ms', as) ← goSeq ms as
      pure (m' :: ms', as)

/-- Mirrors `Mixfix.to_string` with `render_atom` for the atoms and `%` for
the holes; the canonical spelling the decoders compare cases by. -/
def to_string {α : Type} (m : t α) : String := "`" ++ go m ++ "`"
where
  /-- Mirrors `render_atom`: the lossy display glyph. -/
  render (a : Atom.t) : String :=
    match a with
    | .Keyword id => id
    | .Tag "EMPTY" => "/* empty */"
    | .Tag id => "_" ++ id
    | .Operator s => s
    | .LAngle => "<" | .RAngle => ">" | .LParen => "(" | .RParen => ")"
    | .LBrack => "[" | .RBrack => "]" | .LBrace => "{" | .RBrace => "}"
    | a => Atom.string_of_atom a
  /-- The inner `to_string'`. -/
  go : t α → String
    | .Arg _ => "%"
    | .Atom a => render a.it
    | .Brack l m r => render l.it ++ go m ++ render r.it
    | .Infix l a r => go l ++ render a.it ++ go r
    | .Seq ms => " ".intercalate (ms.map go)

end P4SpecTec.Domain.Mixfix
