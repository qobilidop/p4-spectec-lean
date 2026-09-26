import P4SpecTec.Runtime.Type.Typdef
import P4SpecTec.Runtime.Type.Subst

/-!
Type expansion. Mirrors `p4spec/lib/runtime/type/expand.ml`, trusted at
the pinned upstream revision. The recursive alias chase uses explicit fuel;
exhaustion is `none`, distinct from an unknown type or arity error.
-/

namespace P4SpecTec.Runtime.Type.Expand

open P4SpecTec.Lang.Il
open P4SpecTec.Runtime.Type

/-- The type-definition lookup supplied by an interpreter context. -/
abbrev FindTypdef := String → Option Typdef.t

/-- Mirrors `expand_typ`: only a top-level plain alias is unfolded. -/
def expand_typ : Nat → FindTypdef → typ → Subst.Checked typ
  | 0, _, _ => Subst.exhausted
  | fuel + 1, find_typdef_opt, typ => do
    match typ.it with
    | .VarT tid targs =>
      match find_typdef_opt tid.it with
      | none => throw s!"type variable {tid.it} is not defined"
      | some (.Defined tparams deftyp) =>
        match deftyp.it with
        | .PlainT inner =>
          if targs.length != tparams.length then
            throw "type arguments do not match"
          let theta ← Subst.of_lists_checked tparams targs
          let expanded ← Subst.subst_typ_checked Subst.fuel theta inner
          expand_typ fuel find_typdef_opt expanded
        | _ => pure typ
      | some _ => pure typ
    | _ => pure typ

end P4SpecTec.Runtime.Type.Expand
