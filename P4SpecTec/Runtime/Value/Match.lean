import P4SpecTec.Runtime.Value.Value
import P4SpecTec.Runtime.Type.Typdef
import P4SpecTec.Runtime.Type.Subst
import P4SpecTec.Runtime.Type.Equiv

/-!
Whether a value belongs to a type, with subtyping, and the subtype checks
the AL inserts. Mirrors `p4spec/lib/runtime/value/match.ml`, TRUSTED
(design section 5.2). Deviations, listed in the design: the functions
take a fuel, since `sub_` recurses through type aliases and not through
the value; the caches (`cache_sub_var`, `cache_find_typdef_opt`) are
performance devices and are not mirrored; the `FuncT` case, which
compares function signatures with `Type.Equiv`, yields `false` in the
legacy total API. The checked interpreter API below supports bounded
function equivalence and preserves errors and exhaustion separately.
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

/-- A signature finder preserving parameter-conversion exhaustion and errors. -/
abbrev FindFuncChecked := String → Subst.Checked (Option (List tparam × List typ × typ))

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

/-! Checked interpreter entry points. The total Boolean API above remains
available to older proof clients; these definitions do not turn malformed
types, higher-order substitution or fuel exhaustion into a negative match. -/

mutual

/-- Checked `sub_`, including upstream's function-signature equivalence. -/
def sub_checked (find_typdef_opt : FindTypdef) (find_func_opt : FindFuncChecked) :
    Nat → typ → value → Subst.Checked Bool
  | 0, _, _ => Subst.exhausted
  | depth + 1, typ, value => do
    match typ.it with
    | .BoolT => return match value.it with | .BoolV _ => true | _ => false
    | .NumT .NatT =>
      return match value.it with
        | .NumV (.Nat _) => true
        | .NumV (.Int i) => decide (i ≥ 0)
        | _ => false
    | .NumT .IntT => return match value.it with | .NumV _ => true | _ => false
    | .TextT => return match value.it with | .TextV _ => true | _ => false
    | .VarT tid targs =>
      match find_typdef_opt tid.it with
      | none => throw s!"type variable {tid.it} is not defined"
      | some .Param | some (.Defining _) => throw "unexpected type variable"
      | some .Extern => return match value.it with | .ExternV _ => true | _ => false
      | some (.Defined tparams deftyp) =>
        match deftyp.it, value.it with
        | .PlainT inner, _ =>
          if tparams.length != targs.length then throw "List.fold_left2"
          let theta ← Subst.of_lists_checked tparams targs
          let expanded ← Subst.subst_typ_checked Subst.fuel theta inner
          sub_checked find_typdef_opt find_func_opt depth expanded value
        | .StructT typfields, .StructV valuefields =>
          if typfields.length != valuefields.length then return false
          if tparams.length != targs.length then throw "List.fold_left2"
          let theta ← Subst.of_lists_checked tparams targs
          for ((atom_t, inner), (atom_v, field)) in typfields.zip valuefields do
            if !Atom.eq atom_t.it atom_v.it then return false
            let expanded ← Subst.subst_typ_checked Subst.fuel theta inner
            if !(← sub_checked find_typdef_opt find_func_opt depth expanded field) then
              return false
          return true
        | .VariantT cases, .CaseV valuecase =>
          if tparams.length != targs.length then throw "List.fold_left2"
          let theta ← Subst.of_lists_checked tparams targs
          for case in cases do
            if Mixfix.eq_mixop case.nottyp.it valuecase then
              let substituted ← Subst.subst_nottyp_checked Subst.fuel theta case.nottyp
              if (← subs_checked find_typdef_opt find_func_opt depth
                    (Mixfix.args substituted.it) (Mixfix.args valuecase)) then return true
          return false
        | _, _ => return false
    | .TupleT typs =>
      match value.it with
      | .TupleV values => subs_checked find_typdef_opt find_func_opt depth typs values
      | _ => pure false
    | .IterT inner .Opt =>
      match value.it with
      | .OptV (some v) => sub_checked find_typdef_opt find_func_opt depth inner v
      | .OptV none => pure true
      | _ => pure true
    | .IterT inner .List =>
      match value.it with
      | .ListV values => do
        for v in values do
          if !(← sub_checked find_typdef_opt find_func_opt depth inner v) then return false
        return true
      | _ => pure false
    | .FuncT tparams params ret =>
      match value.it with
      | .FuncV fid =>
        match ← find_func_opt fid.it with
        | some (otherTparams, otherParams, otherRet) =>
          Equiv.equiv_functyp find_typdef_opt tparams params ret
            otherTparams otherParams otherRet
        | none => pure false
      | _ => pure false

/-- Checked pairwise subtyping, preserving short-circuit order. -/
def subs_checked (find_typdef_opt : FindTypdef) (find_func_opt : FindFuncChecked)
    (depth : Nat) (typs : List typ) (values : List value) : Subst.Checked Bool := do
  if typs.length != values.length then return false
  for (typ, value) in typs.zip values do
    if !(← sub_checked find_typdef_opt find_func_opt depth typ value) then return false
  return true

end

/-- Checked `check`, with distinct mismatch, hard error and exhaustion. -/
def check_checked (find_typdef_opt : FindTypdef) (find_func_opt : FindFuncChecked) :
    Nat → subcheck → value → Subst.Checked Bool
  | 0, _, _ => Subst.exhausted
  | depth + 1, subcheck, value => do
    match subcheck, value.it with
    | .SkipSC, _ => return true
    | .MixopSC mixops, .CaseV valuecase =>
      return mixops.any fun mixop => Mixfix.eq_mixop mixop valuecase
    | .TupleSC checks, .TupleV values =>
      if checks.length != values.length then return false
      for (check, v) in checks.zip values do
        if !(← check_checked find_typdef_opt find_func_opt depth check v) then return false
      return true
    | .IterSC .Opt _, .OptV none => return true
    | .IterSC .Opt check, .OptV (some v) =>
      check_checked find_typdef_opt find_func_opt depth check v
    | .IterSC .List check, .ListV values =>
      for v in values do
        if !(← check_checked find_typdef_opt find_func_opt depth check v) then return false
      return true
    | .RecurseSC typ, _ => sub_checked find_typdef_opt find_func_opt fuel typ value
    | _, _ => return false

end P4SpecTec.Runtime.Value.Match
