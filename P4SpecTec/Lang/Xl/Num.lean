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

/-- Mirrors `compare`: naturals before integers. -/
def compare : t → t → Ordering
  | .Nat a, .Nat b => Ord.compare a b
  | .Int a, .Int b => Ord.compare a b
  | .Nat _, .Int _ => .lt
  | .Int _, .Nat _ => .gt

/-- Mirrors `compare_typ`. -/
def compare_typ : typ → typ → Ordering
  | .NatT, .NatT => .eq
  | .IntT, .IntT => .eq
  | .NatT, .IntT => .lt
  | .IntT, .NatT => .gt

/-- Mirrors `eq`. -/
def eq (a b : t) : Bool := compare a b == .eq

/-- Mirrors `equiv`. -/
def equiv (a b : typ) : Bool := a == b

/-- Mirrors `sub`: `nat` is a subtype of `int`. -/
def sub (a b : typ) : Bool :=
  match a, b with
  | .NatT, .IntT => true
  | _, _ => equiv a b

/-- Mirrors `un`. -/
def un : unop → t → t
  | .PlusOp, n => n
  | .MinusOp, .Nat n => .Int (-(n : Int))
  | .MinusOp, .Int i => .Int (-i)

/-- Mirrors `bin`; `none` where the OCaml match has no case and raises:
division and modulus by zero, `^`, operands of different kinds. Division
and modulus truncate toward zero (`Bigint.( / )`, `Bigint.rem`). -/
def bin : binop → t → t → Option t
  | .AddOp, .Nat a, .Nat b => some (.Nat (a + b))
  | .AddOp, .Int a, .Int b => some (.Int (a + b))
  | .SubOp, .Nat a, .Nat b => some (.Int ((a : Int) - (b : Int)))
  | .SubOp, .Int a, .Int b => some (.Int (a - b))
  | .MulOp, .Nat a, .Nat b => some (.Nat (a * b))
  | .MulOp, .Int a, .Int b => some (.Int (a * b))
  | .DivOp, .Nat a, .Nat b => if b != 0 then some (.Nat (a / b)) else none
  | .DivOp, .Int a, .Int b => if b != 0 then some (.Int (Int.tdiv a b)) else none
  | .ModOp, .Nat a, .Nat b => if b != 0 then some (.Nat (a % b)) else none
  | .ModOp, .Int a, .Int b => if b != 0 then some (.Int (Int.tmod a b)) else none
  | _, _, _ => none

/-- Mirrors `cmp`; `none` for operands of different kinds (`assert false`). -/
def cmp : cmpop → t → t → Option Bool
  | .LtOp, .Nat a, .Nat b => some (decide (a < b))
  | .LtOp, .Int a, .Int b => some (decide (a < b))
  | .GtOp, .Nat a, .Nat b => some (decide (a > b))
  | .GtOp, .Int a, .Int b => some (decide (a > b))
  | .LeOp, .Nat a, .Nat b => some (decide (a ≤ b))
  | .LeOp, .Int a, .Int b => some (decide (a ≤ b))
  | .GeOp, .Nat a, .Nat b => some (decide (a ≥ b))
  | .GeOp, .Int a, .Int b => some (decide (a ≥ b))
  | _, _, _ => none

end P4SpecTec.Lang.Xl.Num
