import P4SpecTec.Runtime.Value.Value
import P4SpecTec.Runtime.Type.Typdef
import P4SpecTec.Runtime.Type.Subst

/-!
Whether a value belongs to a type, with subtyping, and the subtype checks
the AL inserts. Mirrors `p4spec/lib/runtime/value/match.ml`, TRUSTED
(design section 5.2). Deviations, listed in the design: the functions
take a fuel, since `sub_` recurses through type aliases and not through
the value; the caches (`cache_sub_var`, `cache_find_typdef_opt`) are
performance devices and are not mirrored; the `FuncT` case, which
compares function signatures with `Type.Equiv`, is not ported and yields
`false`, since Nano-P4 has no function values (an M3 item).
-/

namespace P4SpecTec.Runtime.Value.Match

open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Xl
open P4SpecTec.Lang.Il
open P4SpecTec.Runtime.Type

/-- The finder of a type definition (`Ctx.find_typdef_opt`). -/
abbrev FindTypdef := String → Option Typdef.t

/-- The finder of a function signature (`Ctx.find_func_signature_opt`). -/
abbrev FindFunc := String → Option (List tparam × List typ × typ)

mutual

/-- Mirrors `sub_`, with fuel. -/
def sub_ (find_typdef_opt : FindTypdef) (find_func_opt : FindFunc) : Nat → typ → value → Bool
  | 0, _, _ => false
  | fuel + 1, typ, value =>
    match typ.it with
    | .BoolT => match value.it with | .BoolV _ => true | _ => false
    | .NumT .NatT =>
      match value.it with
      | .NumV (.Nat _) => true
      | .NumV (.Int i) => decide (i ≥ 0)
      | _ => false
    | .NumT .IntT => match value.it with | .NumV _ => true | _ => false
    | .TextT => match value.it with | .TextV _ => true | _ => false
    | .VarT tid targs =>
      match find_typdef_opt tid.it with
      | none => false   -- `Option.get` raises upstream
      | some .Param | some (.Defining _) => false   -- an error upstream
      | some .Extern => match value.it with | .ExternV _ => true | _ => false
      | some (.Defined tparams deftyp) =>
        match deftyp.it, value.it with
        | .PlainT typ', _ =>
          let theta := Subst.of_lists tparams targs
          sub_ find_typdef_opt find_func_opt fuel (Subst.subst_typ theta typ') value
        | .StructT typfields, .StructV valuefields =>
          typfields.length == valuefields.length &&
            let theta := Subst.of_lists tparams targs
            (typfields.zip valuefields).all fun ((atom_t, typ'), (atom_v, value')) =>
              Atom.eq atom_t.it atom_v.it &&
                sub_ find_typdef_opt find_func_opt fuel (Subst.subst_typ theta typ') value'
        | .VariantT typcases, .CaseV valuecase =>
          let theta := Subst.of_lists tparams targs
          let values := Mixfix.args valuecase
          typcases.any fun c =>
            Mixfix.eq_mixop c.nottyp.it valuecase &&
              let nottyp := Subst.subst_nottyp theta c.nottyp
              subs_ find_typdef_opt find_func_opt fuel (Mixfix.args nottyp.it) values
        | _, _ => false
    | .TupleT typs =>
      match value.it with
      | .TupleV values =>
        typs.length == values.length &&
          (typs.zip values).all fun (t, v) => sub_ find_typdef_opt find_func_opt fuel t v
      | _ => false
    | .IterT typ_inner .Opt =>
      match value.it with
      | .OptV (some value_inner) => sub_ find_typdef_opt find_func_opt fuel typ_inner value_inner
      | .OptV none => true
      | _ => true
    | .IterT typ_inner .List =>
      match value.it with
      | .ListV values => values.all (sub_ find_typdef_opt find_func_opt fuel typ_inner)
      | _ => false
    | .FuncT _ _ _ => false   -- deviation: `Type.Equiv.equiv_functyp` is not ported

/-- Mirrors `subs_`. -/
def subs_ (find_typdef_opt : FindTypdef) (find_func_opt : FindFunc) (fuel : Nat) (typs : List typ)
    (values : List value) : Bool :=
  typs.length == values.length &&
    (typs.zip values).all fun (t, v) => sub_ find_typdef_opt find_func_opt fuel t v

end

/-- The fuel: deeper than any chain of type aliases. -/
def fuel : Nat := 1000

/-- Mirrors `sub`, without the cache. -/
def sub (find_typdef_opt : FindTypdef) (find_func_opt : FindFunc) (typ : typ) (value : value) :
    Bool :=
  sub_ find_typdef_opt find_func_opt fuel typ value

/-- Mirrors `subs`. -/
def subs (find_typdef_opt : FindTypdef) (find_func_opt : FindFunc) (typs : List typ)
    (values : List value) : Bool :=
  subs_ find_typdef_opt find_func_opt fuel typs values

/-- Mirrors `check`, with fuel: the subtype check the AL inserts at `e <: T`. -/
def check' (find_typdef_opt : FindTypdef) (find_func_opt : FindFunc) : Nat → subcheck → value → Bool
  | 0, _, _ => false
  | fuel + 1, subcheck, value =>
    match subcheck, value.it with
    | .SkipSC, _ => true
    | .MixopSC mixops, .CaseV valuecase => mixops.any fun mixop => Mixfix.eq_mixop mixop valuecase
    | .TupleSC subchecks, .TupleV values =>
      subchecks.length == values.length &&
        (subchecks.zip values).all fun (sc, v) => check' find_typdef_opt find_func_opt fuel sc v
    | .IterSC .Opt _, .OptV none => true
    | .IterSC .Opt subcheck, .OptV (some value') =>
      check' find_typdef_opt find_func_opt fuel subcheck value'
    | .IterSC .List subcheck, .ListV values =>
      values.all (check' find_typdef_opt find_func_opt fuel subcheck)
    | .RecurseSC typ, _ => sub find_typdef_opt find_func_opt typ value
    | _, _ => false

/-- Mirrors `check`. -/
def check (find_typdef_opt : FindTypdef) (find_func_opt : FindFunc) (subcheck : subcheck)
    (value : value) : Bool :=
  check' find_typdef_opt find_func_opt fuel subcheck value

end P4SpecTec.Runtime.Value.Match
