import P4SpecTec.Runtime.Type.Typ

/-!
Substitution of type variables. Mirrors `p4spec/lib/runtime/type/subst.ml`.
A substitution `theta` is an association list from type parameter names
to types (`TIdMap.t` upstream). Deviations, listed in the design: the
recursion takes a fuel; the fresh names `freshen_tparams` invents for
the type parameters of a function type come from the parameter's own
name (`"__FRESH" ++ name`) rather than a global counter; a higher-order
substitution (a type parameter applied to arguments), which upstream
rejects with an error, substitutes the head anyway.
-/

namespace P4SpecTec.Runtime.Type.Subst

open P4SpecTec.Util.Source
open P4SpecTec.Lang.Il

/-- Mirrors `theta = Typ.t TIdMap.t`. -/
abbrev theta := List (String × Typ.t)

/-- Mirrors `TIdMap.of_lists`: parameters zipped with arguments, the
first binding of a name winning on lookup. -/
def of_lists (tparams : List tparam) (typs : List Typ.t) : theta :=
  (tparams.map (·.it)).zip typs

/-- Mirrors `freshen_tparams` (deviation: deterministic fresh names). -/
def freshen_tparams (tparams : List tparam) : theta × List tparam :=
  tparams.foldl (fun (theta, tids_fresh) tp =>
    let tid_fresh : tparam := mkPhrase ("__FRESH" ++ tp.it)
    let typ_fresh : Typ.t := mkPhrase (.VarT tid_fresh [])
    (theta ++ [(tp.it, typ_fresh)], tids_fresh ++ [tid_fresh])) ([], [])

/-- The fuel of the substitutions: deeper than any type. -/
def fuel : Nat := 1000

mutual

/-- Mirrors `subst_typ_inner`, with fuel (deviation: the OCaml recurses on
the type; a type is never as deep as the fuel). -/
def subst_typ_inner (theta : theta) : Nat → typ → typ
  | 0, typ => typ
  | fuel + 1, typ =>
    match typ.it with
    | .BoolT | .NumT _ | .TextT => typ
    | .VarT tid targs =>
      match theta.lookup tid.it with
      | some typ' => typ'
      | none => { typ with it := .VarT tid (subst_typs_inner theta fuel targs) }
    | .TupleT typs => { typ with it := .TupleT (subst_typs_inner theta fuel typs) }
    | .IterT typ' iter => { typ with it := .IterT (subst_typ_inner theta fuel typ') iter }
    | .FuncT tparams typs_params typ_ret =>
      let (theta_fresh, tparams) := freshen_tparams tparams
      let typs_params :=
        subst_typs_inner theta fuel (subst_typs_inner theta_fresh fuel typs_params)
      let typ_ret := subst_typ_inner theta fuel (subst_typ_inner theta_fresh fuel typ_ret)
      { typ with it := .FuncT tparams typs_params typ_ret }

/-- Mirrors `subst_typs_inner`. -/
def subst_typs_inner (theta : theta) (fuel : Nat) : List typ → List typ
  | [] => []
  | t :: ts => subst_typ_inner theta fuel t :: subst_typs_inner theta fuel ts

end

/-- Mirrors `subst_typ`. -/
def subst_typ (theta : theta) (t : typ) : typ :=
  if theta.isEmpty then t else subst_typ_inner theta fuel t

/-- Mirrors `subst_typs`. -/
def subst_typs (theta : theta) (typs : List typ) : List typ :=
  if theta.isEmpty then typs else subst_typs_inner theta fuel typs

/-- Mirrors `subst_nottyp`. -/
def subst_nottyp (theta : theta) (n : nottyp) : nottyp :=
  if theta.isEmpty then n
  else { n with it := Domain.Mixfix.map (subst_typ theta) n.it }

/-- Mirrors `subst_typcase`. -/
def subst_typcase (theta : theta) : typcase → typcase
  | .mk nottyp typorigin hints =>
    let nottyp := subst_nottyp theta nottyp
    let typorigin := match typorigin.it with
      | .mk i targs => { typorigin with it := .mk i (subst_typs theta targs) }
    .mk nottyp typorigin hints

mutual

/-- Mirrors `subst_param`, with fuel. -/
def subst_param (theta : theta) : Nat → param → param
  | 0, param => param
  | fuel + 1, param =>
    match param.it with
    | .ExpP typ => { param with it := .ExpP (subst_typ theta typ) }
    | .DefP i tparams params typ =>
      let (theta_fresh, tparams) := freshen_tparams tparams
      let params := subst_params theta fuel (subst_params theta_fresh fuel params)
      let typ := subst_typ theta (subst_typ theta_fresh typ)
      { param with it := .DefP i tparams params typ }

/-- Mirrors `subst_params`. -/
def subst_params (theta : theta) (fuel : Nat) : List param → List param
  | [] => []
  | p :: ps => subst_param theta fuel p :: subst_params theta fuel ps

end

end P4SpecTec.Runtime.Type.Subst
