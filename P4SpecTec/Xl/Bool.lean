/-!
Booleans and their operators. Mirrors `p4spec/lib/lang/xl/bool.ml`.
-/

namespace P4SpecTec.Xl.Bool

/-- Mirrors `Bool.t` (`` `BoolT ``). -/
inductive t where
  /-- `bool` -/
  | BoolT
  deriving BEq, Repr, Inhabited

/-- Mirrors `Bool.typ` (`` `BoolT ``). -/
inductive typ where
  /-- `bool` -/
  | BoolT
  deriving BEq, Repr, Inhabited

/-- Mirrors `Bool.unop`. -/
inductive unop where
  /-- `~` -/
  | NotOp
  deriving BEq, Repr, Inhabited

/-- Mirrors `Bool.binop`. -/
inductive binop where
  /-- `/\` -/
  | AndOp
  /-- `\/` -/
  | OrOp
  /-- `=>` -/
  | ImplOp
  /-- `<=>` -/
  | EquivOp
  deriving BEq, Repr, Inhabited

/-- Mirrors `Bool.cmpop`. -/
inductive cmpop where
  /-- `=` -/
  | EqOp
  /-- `=/=` -/
  | NeOp
  deriving BEq, Repr, Inhabited

end P4SpecTec.Xl.Bool
