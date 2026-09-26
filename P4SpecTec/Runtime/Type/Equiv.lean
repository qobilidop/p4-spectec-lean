import P4SpecTec.Runtime.Type.Expand
import P4SpecTec.Domain.Mixfix
import P4SpecTec.Lang.Xl.Num

/-!
Type equivalence. Mirrors `p4spec/lib/runtime/type/equiv.ml`, trusted at
the pinned upstream revision. A function signature's paired binders use
the same private, unlexable marker before alias expansion; no marker
escapes this Boolean comparison.
-/

namespace P4SpecTec.Runtime.Type.Equiv

open P4SpecTec.Lang.Il
open P4SpecTec.Runtime.Type

/-- The fixed recursion budget for type equivalence and alias expansion. -/
def fuel : Nat := 1000

mutual

/-- Mirrors `equiv_typ`, with explicit recursion fuel. -/
def equiv_typ_inner (find_typdef_opt : Expand.FindTypdef) : Nat → typ → typ → Subst.Checked Bool
  | 0, _, _ => Subst.exhausted
  | fuel + 1, typ_a, typ_b => do
    let typ_a ← Expand.expand_typ fuel find_typdef_opt typ_a
    let typ_b ← Expand.expand_typ fuel find_typdef_opt typ_b
    match typ_a.it, typ_b.it with
    | .BoolT, .BoolT => pure true
    | .NumT a, .NumT b => pure (P4SpecTec.Lang.Xl.Num.equiv a b)
    | .TextT, .TextT => pure true
    | .VarT tid_a targs_a, .VarT tid_b targs_b =>
      if tid_a.it != tid_b.it || targs_a.length != targs_b.length then pure false
      else equiv_typs_inner find_typdef_opt fuel targs_a targs_b
    | .TupleT typs_a, .TupleT typs_b =>
      if typs_a.length != typs_b.length then pure false
      else equiv_typs_inner find_typdef_opt fuel typs_a typs_b
    | .IterT inner_a iter_a, .IterT inner_b iter_b =>
      if !(← equiv_typ_inner find_typdef_opt fuel inner_a inner_b) then pure false
      else pure (iter_a == iter_b)
    | _, _ => pure false

/-- Pairwise recursive type comparison, after checking arity. -/
def equiv_typs_inner (find_typdef_opt : Expand.FindTypdef) (fuel : Nat) :
    List typ → List typ → Subst.Checked Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if !(← equiv_typ_inner find_typdef_opt fuel a b) then return false
    equiv_typs_inner find_typdef_opt fuel as bs
  | _, _ => pure false

end

/-- Mirrors `equiv_typ` at the top level. -/
def equiv_typ (find_typdef_opt : Expand.FindTypdef) (a b : typ) :
    Subst.Checked Bool :=
  equiv_typ_inner find_typdef_opt fuel a b

mutual

/-- Checked `Mixfix.eq` traversal, preserving the upstream order of
argument checks relative to later atoms and branches. -/
def equiv_nottyp_inner (find_typdef_opt : Expand.FindTypdef) :
    P4SpecTec.Domain.Mixfix.t typ → P4SpecTec.Domain.Mixfix.t typ → Subst.Checked Bool
  | .Arg a, .Arg b => equiv_typ find_typdef_opt a b
  | .Atom a, .Atom b => pure (P4SpecTec.Domain.Atom.eq a.it b.it)
  | .Brack la ma ra, .Brack lb mb rb => do
    if !P4SpecTec.Domain.Atom.eq la.it lb.it then return false
    if !(← equiv_nottyp_inner find_typdef_opt ma mb) then return false
    pure (P4SpecTec.Domain.Atom.eq ra.it rb.it)
  | .Infix la aa ra, .Infix lb ab rb => do
    if !P4SpecTec.Domain.Atom.eq aa.it ab.it then return false
    if !(← equiv_nottyp_inner find_typdef_opt la lb) then return false
    equiv_nottyp_inner find_typdef_opt ra rb
  | .Seq as, .Seq bs => equiv_nottyps_inner find_typdef_opt as bs
  | _, _ => pure false

/-- Checked `Mixfix.eqs`, short-circuiting each branch. -/
def equiv_nottyps_inner (find_typdef_opt : Expand.FindTypdef) :
    List (P4SpecTec.Domain.Mixfix.t typ) →
    List (P4SpecTec.Domain.Mixfix.t typ) → Subst.Checked Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if !(← equiv_nottyp_inner find_typdef_opt a b) then return false
    equiv_nottyps_inner find_typdef_opt as bs
  | _, _ => pure false

end

/-- Mirrors `equiv_nottyp` with the source mixfix traversal order. -/
def equiv_nottyp (find_typdef_opt : Expand.FindTypdef) (a b : nottyp) :
    Subst.Checked Bool := equiv_nottyp_inner find_typdef_opt a.it b.it

/-- A binder marker that cannot be an identifier parsed from a `.watsup`
source. It is internal to equivalence and does not appear in returned data. -/
def binder_marker (index : Nat) : String := "\u0000P4SpecTec.Type.Equiv#" ++ toString index

/-- Mirrors bounded `equiv_functyp`: paired binders are alpha-equivalent.
Nested function substitution requiring observable type-fresh allocation
remains explicitly unsupported, rather than using deterministic names. -/
def equiv_functyp (find_typdef_opt : Expand.FindTypdef)
    (tparams_a : List tparam) (params_a : List typ) (ret_a : typ)
    (tparams_b : List tparam) (params_b : List typ) (ret_b : typ) :
    Subst.Checked Bool := do
  if tparams_a.length != tparams_b.length || params_a.length != params_b.length then
    return false
  let markers := (List.range tparams_a.length).map fun index =>
    P4SpecTec.Util.Source.mkPhrase (.VarT
      (P4SpecTec.Util.Source.mkPhrase (binder_marker index)) [])
  let theta_a ← Subst.of_lists_checked tparams_a markers
  let theta_b ← Subst.of_lists_checked tparams_b markers
  let find_fresh : Expand.FindTypdef := fun name =>
    if (List.range tparams_a.length).any (fun i => binder_marker i == name) then
      some .Param
    else find_typdef_opt name
  let params_a ← Subst.subst_typs_checked Subst.fuel theta_a params_a
  let params_b ← Subst.subst_typs_checked Subst.fuel theta_b params_b
  let ret_a ← Subst.subst_typ_checked Subst.fuel theta_a ret_a
  let ret_b ← Subst.subst_typ_checked Subst.fuel theta_b ret_b
  if !(← equiv_typs_inner find_fresh fuel params_a params_b) then
    return false
  equiv_typ_inner find_fresh fuel ret_a ret_b

end P4SpecTec.Runtime.Type.Equiv
