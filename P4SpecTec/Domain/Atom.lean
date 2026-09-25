/-!
Atoms: the keywords, tags and operator symbols of mixfix notation.
Mirrors `p4spec/lib/domain/atom.ml`, constructor for constructor.
-/

namespace P4SpecTec.Domain.Atom

/-- Mirrors `Atom.t`. -/
inductive t where
  /-- concrete object word: INT -/
  | Keyword (id : String)
  /-- silent meta case label: _NUM -/
  | Tag (id : String)
  /-- concrete operator: '+', '->', '#' -/
  | Operator (s : String)
  /-- `<:` -/
  | Sub
  /-- `:>` -/
  | Sup
  /-- `|-` -/
  | Turnstile
  /-- `-|` -/
  | Tilesturn
  /-- `->` -/
  | Arrow
  /-- `->_` -/
  | ArrowSub
  /-- `=>_` -/
  | DoubleArrowSub
  /-- `==>` -/
  | DoubleArrowLong
  /-- `~>` -/
  | SqArrow
  /-- `~>*` -/
  | SqArrowStar
  /-- `.` -/
  | Dot
  /-- `..` -/
  | Dot2
  /-- `...` -/
  | Dot3
  /-- `;` -/
  | Semicolon
  /-- `:` -/
  | Colon
  /-- `:=` -/
  | ColonEq
  /-- `~~` -/
  | Tilde2
  /-- `\` -/
  | Backslash
  /-- `` `< `` -/
  | LAngle
  /-- `` `> `` -/
  | RAngle
  /-- `` `( `` -/
  | LParen
  /-- `` `) `` -/
  | RParen
  /-- `` `[ `` -/
  | LBrack
  /-- `` `] `` -/
  | RBrack
  /-- `` `{ `` -/
  | LBrace
  /-- `` `} `` -/
  | RBrace
  deriving BEq, Repr, Inhabited

/-- Mirrors `string_of_atom`: the parse-faithful spelling. -/
def string_of_atom : t → String
  | .Keyword id => id
  | .Tag id => "_" ++ id
  | .Operator s => "'" ++ s ++ "'"
  | .Sub => "<:"
  | .Sup => ":>"
  | .Turnstile => "|-"
  | .Tilesturn => "-|"
  | .Arrow => "->"
  | .ArrowSub => "->_"
  | .DoubleArrowSub => "=>_"
  | .DoubleArrowLong => "==>"
  | .SqArrow => "~>"
  | .SqArrowStar => "~>*"
  | .Dot => "."
  | .Dot2 => ".."
  | .Dot3 => "..."
  | .Semicolon => ";"
  | .Colon => ":"
  | .ColonEq => ":="
  | .Tilde2 => "~~"
  | .Backslash => "\\"
  | .LAngle => "`<"
  | .RAngle => "`>"
  | .LParen => "`("
  | .RParen => "`)"
  | .LBrack => "`["
  | .RBrack => "`]"
  | .LBrace => "`{"
  | .RBrace => "`}"

/-- The constructor's position in the declaration, for `compare`
(`Stdlib.compare` on OCaml constructors orders constant constructors before
non-constant ones by declaration order; `Keyword`, `Tag` and `Operator` carry
a string, so they come after every symbol). -/
def tag : t → Nat
  | .Sub => 0 | .Sup => 1 | .Turnstile => 2 | .Tilesturn => 3 | .Arrow => 4
  | .ArrowSub => 5 | .DoubleArrowSub => 6 | .DoubleArrowLong => 7 | .SqArrow => 8
  | .SqArrowStar => 9 | .Dot => 10 | .Dot2 => 11 | .Dot3 => 12 | .Semicolon => 13
  | .Colon => 14 | .ColonEq => 15 | .Tilde2 => 16 | .Backslash => 17 | .LAngle => 18
  | .RAngle => 19 | .LParen => 20 | .RParen => 21 | .LBrack => 22 | .RBrack => 23
  | .LBrace => 24 | .RBrace => 25
  | .Keyword _ => 26 | .Tag _ => 27 | .Operator _ => 28

/-- Mirrors `Atom.compare` (`Stdlib.compare` on the OCaml representation:
constant constructors first in declaration order, then block constructors in
declaration order, strings compared lexicographically). -/
def compare (a b : t) : Ordering :=
  match a, b with
  | .Keyword x, .Keyword y => Ord.compare x y
  | .Tag x, .Tag y => Ord.compare x y
  | .Operator x, .Operator y => Ord.compare x y
  | _, _ => Ord.compare (tag a) (tag b)

/-- Mirrors `Atom.eq`. -/
def eq (a b : t) : Bool := compare a b == .eq

end P4SpecTec.Domain.Atom
