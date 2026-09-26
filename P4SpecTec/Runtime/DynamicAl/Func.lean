import P4SpecTec.Lang.Al.Ast
import P4SpecTec.Runtime.Type.Typ

/-!
Functions as the AL interpreter stores them. Mirrors
`p4spec/lib/runtime/dynamic-al/func.ml`.
-/

namespace P4SpecTec.Runtime.Dynamic_al.Func

open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al
open P4SpecTec.Runtime.Type

/-- Mirrors `Func.t`. -/
inductive t where
  /-- An extern function. -/
  | Extern (tparams : List tparam) (params : List param) (typ : typ)
  /-- A builtin function. -/
  | Builtin (tparams : List tparam) (params : List param) (typ : typ)
  /-- A table function. -/
  | Table (params : List param) (typ : typ) (rows : List Lang.Al.tablerow)
  /-- A defined function. -/
  | Defined (tparams : List tparam) (params : List param) (typ : typ)
      (clauses : List Lang.Il.clause) (elseclause : Option Lang.Il.elseclause)

/-- Mirrors `to_string`. -/
def to_string : t → String
  | .Extern .. => "extern function"
  | .Builtin .. => "builtin function"
  | .Table .. => "table function"
  | .Defined .. => "defined function"

/-- Mirrors `get_signature`. -/
def get_signature : t → List tparam × List typ × typ
  | .Extern tparams params typ => (tparams, Typ.Make.of_params_il 1000 params, typ)
  | .Builtin tparams params typ => (tparams, Typ.Make.of_params_il 1000 params, typ)
  | .Table params typ _ => ([], Typ.Make.of_params_il 1000 params, typ)
  | .Defined tparams params typ _ _ => (tparams, Typ.Make.of_params_il 1000 params, typ)

/-- Checked `get_signature`: `none` is nested-parameter fuel exhaustion. -/
def get_signature_checked (depth : Nat) : t → Option (List tparam × List typ × typ)
  | .Extern tparams params typ | .Builtin tparams params typ
  | .Defined tparams params typ _ _ => do
    pure (tparams, ← Typ.Make.of_params_il_checked depth params, typ)
  | .Table params typ _ => do
    pure ([], ← Typ.Make.of_params_il_checked depth params, typ)

end P4SpecTec.Runtime.Dynamic_al.Func
