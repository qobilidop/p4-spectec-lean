/-!
Numbers: natural numbers and integers, and their operators. Mirrors
`p4spec/lib/lang/xl/num.ml`. Bigints become Lean's unbounded `Nat` and
`Int`.
-/

namespace P4SpecTec.Lang.Xl.Num

/-- A number. Mirrors `Num.t` (`` `Nat `` and `` `Int ``). -/
inductive t where
  /-- A natural number. -/
  | Nat (n : _root_.Nat)
  /-- An integer. -/
  | Int (i : _root_.Int)
  deriving BEq, Repr, Inhabited

/-- A number type. Mirrors `Num.typ`. -/
inductive typ where
  /-- `nat` -/
  | NatT
  /-- `int` -/
  | IntT
  deriving BEq, Repr, Inhabited

/-- Mirrors `Num.unop`. -/
inductive unop where
  /-- `+` -/
  | PlusOp
  /-- `-` -/
  | MinusOp
  deriving BEq, Repr, Inhabited

/-- Mirrors `Num.binop`. -/
inductive binop where
  /-- `+` -/
  | AddOp
  /-- `-` -/
  | SubOp
  /-- `*` -/
  | MulOp
  /-- `/` -/
  | DivOp
  /-- `\` -/
  | ModOp
  /-- `^` -/
  | PowOp
  deriving BEq, Repr, Inhabited

/-- Mirrors `Num.cmpop`. -/
inductive cmpop where
  /-- `<` -/
  | LtOp
  /-- `>` -/
  | GtOp
  /-- `<=` -/
  | LeOp
  /-- `>=` -/
  | GeOp
  deriving BEq, Repr, Inhabited

/-- Mirrors `to_typ`. -/
def to_typ : t → typ
  | .Nat _ => .NatT
  | .Int _ => .IntT

/-- Mirrors `to_int`. -/
def to_int : t → Int
  | .Nat n => n
  | .Int i => i

/-- Mirrors `string_of_num`: integers carry an explicit sign. -/
def string_of_num : t → String
  | .Nat n => toString n
  | .Int i => (if i ≥ 0 then "+" else "-") ++ toString i.natAbs

end P4SpecTec.Lang.Xl.Num
