import P4SpecTec.Lang.Il.Ast

/-!
Types at runtime: the constructors. Mirrors
`p4spec/lib/runtime/type/typ.ml` (`Typ.Make`), for the IL; the SL and PL
parameter conversions are not mirrored, since only the AL is ported.
-/

namespace P4SpecTec.Runtime.Type.Typ

open P4SpecTec.Util.Source
open P4SpecTec.Lang.Xl
open P4SpecTec.Lang.Il

/-- Mirrors `Typ.t`. -/
abbrev t := typ

/-! Mirrors `Typ.Make`. -/
namespace Make

/-- Mirrors `iterate`: the type under the iteration dimensions. -/
def iterate (typ : t) (iters : List iter) : t :=
  iters.foldl (fun typ iter => { typ with it := .IterT typ iter }) typ

/-- Mirrors `bool'`. -/
def bool' : typ' := .BoolT

/-- Mirrors `bool`. -/
def bool : t := mkPhrase bool'

/-- Mirrors `nat'`. -/
def nat' : typ' := .NumT .NatT

/-- Mirrors `nat`. -/
def nat : t := mkPhrase nat'

/-- Mirrors `int'`. -/
def int' : typ' := .NumT .IntT

/-- Mirrors `int`. -/
def int : t := mkPhrase int'

/-- Mirrors `num'`. -/
def num' (numtyp : Num.typ) : typ' := .NumT numtyp

/-- Mirrors `num`. -/
def num (numtyp : Num.typ) : t := mkPhrase (num' numtyp)

/-- Mirrors `text'`. -/
def text' : typ' := .TextT

/-- Mirrors `text`. -/
def text : t := mkPhrase text'

/-- Mirrors `var'`. -/
def var' (id : Lang.Il.id) (targs : List targ) : typ' := .VarT id targs

/-- Mirrors `var`. -/
def var (id : Lang.Il.id) (targs : List targ) : t := mkPhrase (var' id targs)

/-- Mirrors `tuple'`. -/
def tuple' (typs : List typ) : typ' := .TupleT typs

/-- Mirrors `tuple`. -/
def tuple (typs : List typ) : t := mkPhrase (tuple' typs)

/-- Mirrors `iter'`. -/
def iter' (typ : typ) (it : iter) : typ' := .IterT typ it

/-- Mirrors `iter`. -/
def iter (typ : typ) (it : Lang.Il.iter) : t := mkPhrase (iter' typ it)

/-- Mirrors `opt'`. -/
def opt' (typ : typ) : typ' := iter' typ .Opt

/-- Mirrors `opt`. -/
def opt (typ : typ) : t := iter typ .Opt

/-- Mirrors `list'`. -/
def list' (typ : typ) : typ' := iter' typ .List

/-- Mirrors `list`. -/
def list (typ : typ) : t := iter typ .List

/-- Mirrors `func'`. -/
def func' (tparams : List tparam) (typs_params : List typ) (typ : typ) : typ' :=
  .FuncT tparams typs_params typ

/-- Mirrors `func`. -/
def func (tparams : List tparam) (typs_params : List typ) (typ : typ) : t :=
  mkPhrase (func' tparams typs_params typ)

mutual

/-- Mirrors `of_param_il`: the type of a parameter, with fuel (deviation:
the OCaml recurses on the parameter). -/
def of_param_il : Nat → param → t
  | 0, param => match param.it with | .ExpP typ => typ | .DefP _ _ _ typ => typ
  | fuel + 1, param =>
    match param.it with
    | .ExpP typ => typ
    | .DefP _ tparams params typ => func tparams (of_params_il fuel params) typ

/-- Mirrors `of_params_il`. -/
def of_params_il (fuel : Nat) : List param → List t
  | [] => []
  | p :: ps => of_param_il fuel p :: of_params_il fuel ps

end

end Make

end P4SpecTec.Runtime.Type.Typ
