import Std.Data.HashMap
import P4SpecTec.AL.Ast
import P4SpecTec.Codegen.Names

/-!
The spec environment the compiler consults: every definition by name,
with the queries codegen needs (a type's parameters and body, a function's
signature, a relation's signature and input positions) and the resolution
of type aliases with type-argument substitution, mirroring what the
interpreter's `Ctx.find_defined_typdef` and `Type.Subst` compute.
-/

namespace P4SpecTec.Codegen

open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.IL
open P4SpecTec.AL

/-- What is known about a type definition. -/
structure TypeInfo where
  /-- The type parameters. -/
  tparams : List String
  /-- The body; `none` for an `extern syntax`. -/
  deftyp : Option deftyp'
  /-- The spec file. -/
  file : String

/-- The kind of a function definition. -/
inductive FuncKind where
  /-- `dec` with clauses. -/
  | defined
  /-- `builtin dec`. -/
  | builtin
  /-- `extern dec`. -/
  | extern
  /-- `table dec`. -/
  | table
  deriving BEq, Repr

/-- What is known about a function. -/
structure FuncInfo where
  /-- The kind. -/
  kind : FuncKind
  /-- The type parameters. -/
  tparams : List String
  /-- The parameters. -/
  params : List param'
  /-- The result type. -/
  ret : typ'
  /-- The spec file. -/
  file : String

/-- What is known about a relation. -/
structure RelInfo where
  /-- Whether it is an `extern relation`. -/
  extern : Bool
  /-- The argument types, in notation order. -/
  args : List typ'
  /-- The input positions. -/
  inputs : List Nat
  /-- The spec file. -/
  file : String

/-- The environment. -/
structure Env where
  /-- The generated library's name, the namespace every reference is qualified with. -/
  lib : String := "Spec"
  /-- Types by name. -/
  types : Std.HashMap String TypeInfo := {}
  /-- Functions by name. -/
  funcs : Std.HashMap String FuncInfo := {}
  /-- Relations by name. -/
  rels : Std.HashMap String RelInfo := {}
  /-- Definitions in spec order. -/
  defs : List AL.def := []

namespace Env

/-- The file a definition comes from. -/
def fileOf (d : AL.def) : String := d.«at».left.file

/-- Qualify a generated name with the library, so a spec variable named
after a type or relation cannot shadow it. -/
def q (env : Env) (name : String) : String := env.lib ++ "." ++ name

/-- Build the environment from a spec. -/
def ofSpec (lib : String) (spec : AL.spec) : Env := Id.run do
  let mut env : Env := { lib, defs := spec }
  for d in spec do
    let file := fileOf d
    match d.it with
    | .ExternTypD i _ =>
      env := { env with types := (env.types.insert i.it { tparams := [], deftyp := none, file }) }
    | .TypD i tparams deftyp _ =>
      env := { env with types := (env.types.insert i.it
        { tparams := tparams.map (·.it), deftyp := some deftyp.it, file }) }
    | .VarD .. => pure ()
    | .ExternRelD i nottyp inputs _ =>
      env := { env with rels := (env.rels.insert i.it
        { extern := true, args := (Mixfix.args nottyp.it).map (·.it),
          inputs := inputs.map (·.toNat), file }) }
    | .RelD i nottyp inputs _ _ _ =>
      env := { env with rels := (env.rels.insert i.it
        { extern := false, args := (Mixfix.args nottyp.it).map (·.it),
          inputs := inputs.map (·.toNat), file }) }
    | .ExternDecD i tparams params typ _ =>
      env := { env with funcs := (env.funcs.insert i.it
        { kind := .extern, tparams := tparams.map (·.it), params := params.map (·.it),
          ret := typ.it, file }) }
    | .BuiltinDecD i tparams params typ _ =>
      env := { env with funcs := (env.funcs.insert i.it
        { kind := .builtin, tparams := tparams.map (·.it), params := params.map (·.it),
          ret := typ.it, file }) }
    | .TableDecD i params typ _ _ =>
      env := { env with funcs := (env.funcs.insert i.it
        { kind := .table, tparams := [], params := params.map (·.it), ret := typ.it, file }) }
    | .FuncDecD i tparams params typ _ _ _ =>
      env := { env with funcs := (env.funcs.insert i.it
        { kind := .defined, tparams := tparams.map (·.it), params := params.map (·.it),
          ret := typ.it, file }) }
  pure env

/-- Substitute type arguments for type parameters. Mirrors `Type.Subst.subst_typ`. -/
partial def substTyp (theta : List (String × typ')) : typ' → typ'
  | .VarT i [] =>
    match theta.lookup i.it with
    | some t => t
    | none => .VarT i []
  | .VarT i targs => .VarT i (targs.map fun t => { t with it := substTyp theta t.it })
  | .TupleT ts => .TupleT (ts.map fun t => { t with it := substTyp theta t.it })
  | .IterT t i => .IterT { t with it := substTyp theta t.it } i
  | .FuncT tps ts t =>
    .FuncT tps (ts.map fun t => { t with it := substTyp theta t.it })
      { t with it := substTyp theta t.it }
  | t => t

/-- Substitute in a notation type. -/
def substNottyp (theta : List (String × typ')) (n : nottyp') : nottyp' :=
  Mixfix.map (fun t => { t with it := substTyp theta t.it }) n

/-- The definition of a type applied to arguments, with the parameters
substituted; `none` for an extern or unknown type. -/
def instantiate (env : Env) (id : String) (targs : List typ') : Option deftyp' := do
  let info ← env.types.get? id
  let body ← info.deftyp
  let theta := info.tparams.zip targs
  pure <| match body with
    | .PlainT t => .PlainT { t with it := substTyp theta t.it }
    | .StructT fields =>
      .StructT (fields.map fun (a, t) => (a, { t with it := substTyp theta t.it }))
    | .VariantT cases => .VariantT (cases.map fun c =>
        .mk { c.nottyp with it := substNottyp theta c.nottyp.it } c.typorigin [])

/-- Unfold type aliases (`PlainT`) at the head, as `upcast` and `downcast`
do in the interpreter. -/
partial def resolve (env : Env) : typ' → typ'
  | .VarT i targs =>
    match env.instantiate i.it (targs.map (·.it)) with
    | some (.PlainT t) => env.resolve t.it
    | _ => .VarT i targs
  | t => t

/-- Whether a type name is an alias. -/
def isAlias (env : Env) (id : String) : Bool :=
  match env.types.get? id with
  | some { deftyp := some (.PlainT _), .. } => true
  | _ => false

/-- The cases of a variant type applied to arguments. -/
def variantCases (env : Env) (id : String) (targs : List typ') : Option (List typcase) :=
  match env.instantiate id targs with
  | some (.VariantT cases) => some cases
  | _ => none

/-- The fields of a struct type applied to arguments. -/
def structFields (env : Env) (id : String) (targs : List typ') : Option (List (atom × typ)) :=
  match env.instantiate id targs with
  | some (.StructT fields) => some fields
  | _ => none

/-- The mixops of a variant's cases, in order. -/
def caseMixops (env : Env) (id : String) : List Mixfix.mixop :=
  match env.variantCases id [] with
  | some cases => cases.map fun c => Mixfix.to_mixop c.nottyp.it
  | none => []

/-- The types named in a type expression. -/
partial def typeRefs : typ' → List String
  | .VarT i targs => i.it :: targs.flatMap fun t => typeRefs t.it
  | .TupleT ts => ts.flatMap fun t => typeRefs t.it
  | .IterT t _ => typeRefs t.it
  | .FuncT _ ts t => ts.flatMap (fun t => typeRefs t.it) ++ typeRefs t.it
  | _ => []

/-- The types named in a type definition body. -/
def deftypRefs : deftyp' → List String
  | .PlainT t => typeRefs t.it
  | .StructT fields => fields.flatMap fun (_, t) => typeRefs t.it
  | .VariantT cases =>
    cases.flatMap fun c => (Mixfix.args c.nottyp.it).flatMap fun t => typeRefs t.it

end Env

end P4SpecTec.Codegen
