import P4SpecTec.Lang.Il.Ast

/-!
Type definitions as the runtime knows them. Mirrors
`p4spec/lib/runtime/type/typdef.ml`.
-/

namespace P4SpecTec.Runtime.Type.Typdef

open P4SpecTec.Lang.Il

/-- Mirrors `Typdef.t`. -/
inductive t where
  /-- A type parameter. -/
  | Param
  /-- An extern type. -/
  | Extern
  /-- A type being defined. -/
  | Defining (tparams : List tparam)
  /-- A type that is completely defined. -/
  | Defined (tparams : List tparam) (deftyp : deftyp)

/-- Mirrors `get_tparams`. -/
def get_tparams : t → List tparam
  | .Param | .Extern => []
  | .Defining tparams => tparams
  | .Defined tparams _ => tparams

end P4SpecTec.Runtime.Type.Typdef
