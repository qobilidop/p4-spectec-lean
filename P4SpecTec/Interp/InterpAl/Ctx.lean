import Std.Data.HashMap
import P4SpecTec.Interp.InterpAl.Backtrack
import P4SpecTec.Runtime.Type.Typdef
import P4SpecTec.Runtime.Type.Subst
import P4SpecTec.Runtime.Dynamic.Var
import P4SpecTec.Runtime.DynamicAl.Rel
import P4SpecTec.Runtime.DynamicAl.Func
import P4SpecTec.Runtime.Value.Value

/-!
The interpreter's context. Mirrors `p4spec/lib/interp/interp-al/ctx.ml`,
TRUSTED (design section 5.2): the same records and functions in the same
order. Deviations, listed in the design: the global tables are immutable
hash maps built once by `init` and threaded through `t`, the local
environments are association lists (the OCaml's `Map`s, with the same
"last binding wins" reading), and the deterministic mode flag `is_det`
is not mirrored, since only the sequential mode is ported.
-/

namespace P4SpecTec.Interp_al.Ctx

open P4SpecTec.Util.Source
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al
open P4SpecTec.Runtime
open P4SpecTec.Runtime.Type
open P4SpecTec.Runtime.Dynamic
open P4SpecTec.Runtime.Dynamic_al
open P4SpecTec.Interp_al.Backtrack
open P4SpecTec.Prelude

/-! Backtracing -/

/-- Mirrors `back_undef`. -/
def back_undef {α : Type} («at» : region) (kind : String) (id : String) : backtrack α :=
  back_err «at» s!"{kind} `{id}` is undefined"

/-- Mirrors `back_dup`. -/
def back_dup {α : Type} («at» : region) (kind : String) (id : String) : backtrack α :=
  back_err «at» s!"{kind} `{id}` was already defined"

/-- Mirrors `error_dup`. -/
def error_dup (_at : region) (kind : String) (id : String) : String :=
  s!"{kind} `{id}` was already defined"

/-! Cursor -/

/-- Mirrors `cursor`. -/
inductive cursor where
  /-- The global tables. -/
  | Global
  /-- The local environments. -/
  | Local
  deriving BEq, Repr

/-! Context -/

/-- Mirrors `global`. -/
structure global where
  /-- Map from syntax ids to type definitions. -/
  tdtbl : Std.HashMap String Typdef.t := {}
  /-- Map from relation ids to relations. -/
  rtbl : Std.HashMap String Rel.t := {}
  /-- Map from function ids to functions. -/
  ftbl : Std.HashMap String Func.t := {}

/-- Mirrors `local`. -/
structure «local» where
  /-- Map from syntax ids to type definitions. -/
  tdenv : List (String × Typdef.t) := []
  /-- Map from function ids to functions. -/
  fenv : List (String × Func.t) := []
  /-- Map from variables to values. -/
  venv : List (Var.t × value) := []

/-- Mirrors `t`. -/
structure t where
  /-- Global layer. -/
  global : global
  /-- Local layer. -/
  «local» : «local»

/-! Adders for globals -/

/-- Mirrors `add_typdef_global`. -/
def add_typdef_global (g : global) (tid : Lang.Il.id) (td : Typdef.t) : Except String global :=
  if g.tdtbl.contains tid.it then throw (error_dup tid.at "type" tid.it)
  else pure { g with tdtbl := g.tdtbl.insert tid.it td }

/-- Mirrors `add_rel_global`. -/
def add_rel_global (g : global) (rid : Lang.Il.id) (rel : Rel.t) : Except String global :=
  if g.rtbl.contains rid.it then throw (error_dup rid.at "relation" rid.it)
  else pure { g with rtbl := g.rtbl.insert rid.it rel }

/-- Mirrors `add_func_global`. -/
def add_func_global (g : global) (fid : Lang.Il.id) (func : Func.t) : Except String global :=
  if g.ftbl.contains fid.it then throw (error_dup fid.at "function" fid.it)
  else pure { g with ftbl := g.ftbl.insert fid.it func }

/-! Global initializer -/

/-- Mirrors `load_def`. -/
def load_def (g : global) (d : Lang.Al.def) : Except String global :=
  match d.it with
  | .ExternTypD i _ => add_typdef_global g i .Extern
  | .TypD i tparams deftyp _ => add_typdef_global g i (.Defined tparams deftyp)
  | .VarD .. => pure g
  | .ExternRelD i nottyp inputs _ => add_rel_global g i (.Extern nottyp inputs)
  | .RelD i nottyp input rulegroups elsegroup_opt _ =>
    add_rel_global g i (.Defined nottyp input rulegroups elsegroup_opt)
  | .ExternDecD i tparams params typ _ => add_func_global g i (.Extern tparams params typ)
  | .BuiltinDecD i tparams params typ _ => add_func_global g i (.Builtin tparams params typ)
  | .TableDecD i params typ tablerows _ => add_func_global g i (.Table params typ tablerows)
  | .FuncDecD i tparams params typ clauses elseclause_opt _ =>
    add_func_global g i (.Defined tparams params typ clauses elseclause_opt)

/-- Mirrors `load_defs`. -/
def load_defs (g : global) : List Lang.Al.def → Except String global
  | [] => pure g
  | d :: ds => do load_defs (← load_def g d) ds

/-- Mirrors `init`: the global tables of a spec. -/
def init (spec : Lang.Al.spec) : Except String global := load_defs {} spec

/-! Constructor -/

/-- Mirrors `empty_local`. -/
def empty_local : «local» := {}

/-- Mirrors `empty`, for the given globals. -/
def empty (g : global) : t := { global := g, «local» := empty_local }

/-! Finders for values -/

/-- Mirrors `find_value_opt`. -/
def find_value_opt (ctx : t) (var : Var.t) : Option value :=
  (ctx.«local».venv.find? fun (v, _) => Var.eq v var).map (·.2)

/-- Mirrors `find_value`. -/
def find_value (ctx : t) (var : Var.t) : backtrack value :=
  match find_value_opt ctx var with
  | some value => pure value
  | none => back_undef var.1.at "value" (Var.to_string var)

/-- Mirrors `find_values`. -/
def find_values (ctx : t) : List Var.t → backtrack (List value)
  | [] => pure []
  | var_h :: vars_t => do
    let value_h ← find_value ctx var_h
    let values_t ← find_values ctx vars_t
    pure (value_h :: values_t)

/-- Mirrors `bound_value`. -/
def bound_value (ctx : t) (var : Var.t) : Bool := (find_value_opt ctx var).isSome

/-! Finders for type definitions -/

/-- Mirrors `find_typdef_opt`: the local layer first. -/
def find_typdef_opt (ctx : t) (tid : Lang.Il.id) : Option Typdef.t :=
  match ctx.«local».tdenv.lookup tid.it with
  | some td => some td
  | none => ctx.global.tdtbl.get? tid.it

/-- `find_typdef_opt` by name, for `Value.Match`. -/
def find_typdef_opt' (ctx : t) (tid : String) : Option Typdef.t :=
  find_typdef_opt ctx (mkPhrase tid)

/-- Mirrors `find_typdef`. -/
def find_typdef (ctx : t) (tid : Lang.Il.id) : backtrack Typdef.t :=
  match find_typdef_opt ctx tid with
  | some td => pure td
  | none => back_undef tid.at "type" tid.it

/-- Mirrors `find_defined_typdef`. -/
def find_defined_typdef (ctx : t) (tid : Lang.Il.id) : backtrack (List tparam × deftyp) := do
  match ← find_typdef ctx tid with
  | .Param | .Extern | .Defining _ => back_undef tid.at "defined type" tid.it
  | .Defined tparams deftyp => pure (tparams, deftyp)

/-- Mirrors `bound_typdef`. -/
def bound_typdef (ctx : t) (tid : Lang.Il.id) : Bool := (find_typdef_opt ctx tid).isSome

/-! Finders for rules -/

/-- Mirrors `find_rel_opt`. -/
def find_rel_opt (ctx : t) (rid : Lang.Il.id) : Option Rel.t := ctx.global.rtbl.get? rid.it

/-- Mirrors `find_rel`. -/
def find_rel (ctx : t) (rid : Lang.Il.id) : backtrack Rel.t :=
  match find_rel_opt ctx rid with
  | some rel => pure rel
  | none => back_undef rid.at "relation" rid.it

/-- Mirrors `find_rel_signature_opt`. -/
def find_rel_signature_opt (ctx : t) (rid : Lang.Il.id) : Option (nottyp × Hints.Input.t) :=
  (find_rel_opt ctx rid).map Rel.get_signature

/-- Mirrors `find_rel_signature`. -/
def find_rel_signature (ctx : t) (rid : Lang.Il.id) : backtrack (nottyp × Hints.Input.t) :=
  match find_rel_signature_opt ctx rid with
  | some sig => pure sig
  | none => back_undef rid.at "relation" rid.it

/-- Mirrors `bound_rel`. -/
def bound_rel (ctx : t) (rid : Lang.Il.id) : Bool := (find_rel_opt ctx rid).isSome

/-! Finders for definitions -/

/-- Mirrors `find_func_opt`: the local layer first, with its cursor. -/
def find_func_opt (ctx : t) (fid : Lang.Il.id) : Option (cursor × Func.t) :=
  match ctx.«local».fenv.lookup fid.it with
  | some func => some (.Local, func)
  | none => (ctx.global.ftbl.get? fid.it).map fun func => (.Global, func)

/-- Mirrors `find_func`. -/
def find_func (ctx : t) (fid : Lang.Il.id) : backtrack (cursor × Func.t) :=
  match find_func_opt ctx fid with
  | some r => pure r
  | none => back_undef fid.at "function" fid.it

/-- Mirrors `find_func_signature_opt`. -/
def find_func_signature_opt (ctx : t) (fid : Lang.Il.id) :
    Option (List tparam × List typ × typ) :=
  (find_func_opt ctx fid).map fun (_, func) => Func.get_signature func

/-- `find_func_signature_opt` by name, for `Value.Match`. -/
def find_func_signature_opt' (ctx : t) (fid : String) : Option (List tparam × List typ × typ) :=
  find_func_signature_opt ctx (mkPhrase fid)

/-- Mirrors `find_func_signature`. -/
def find_func_signature (ctx : t) (fid : Lang.Il.id) : backtrack (List tparam × List typ × typ) :=
  match find_func_signature_opt ctx fid with
  | some sig => pure sig
  | none => back_undef fid.at "function" fid.it

/-- Mirrors `bound_func`. -/
def bound_func (ctx : t) (fid : Lang.Il.id) : Bool := (find_func_opt ctx fid).isSome

/-! Adders -/

/-- Mirrors `add_value`. -/
def add_value (ctx : t) (var : Var.t) (value : value) : t :=
  { ctx with «local» := { ctx.«local» with venv := (var, value) :: ctx.«local».venv } }

/-- Mirrors `add_typdef`. -/
def add_typdef (ctx : t) (tid : Lang.Il.id) (td : Typdef.t) : backtrack t :=
  if bound_typdef ctx tid then back_dup tid.at "type" tid.it
  else pure { ctx with «local» := { ctx.«local» with tdenv := (tid.it, td) :: ctx.«local».tdenv } }

/-- Mirrors `add_func`. -/
def add_func (ctx : t) (fid : Lang.Il.id) (func : Func.t) : backtrack t :=
  if bound_func ctx fid then back_dup fid.at "function" fid.it
  else pure { ctx with «local» := { ctx.«local» with fenv := (fid.it, func) :: ctx.«local».fenv } }

/-! Constructors -/

/-- Mirrors `localize`: a fresh local layer. -/
def localize (ctx : t) : t := { ctx with «local» := empty_local }

/-- Mirrors `transpose`: a matrix of values as batches, one per column;
an error unless every row has the first row's width. -/
def transpose (value_matrix : List (List value)) : backtrack (List (List value)) :=
  match value_matrix with
  | [] => pure []
  | row_h :: _ =>
    let width := row_h.length
    if value_matrix.all fun row => row.length == width then
      pure ((List.range width).map fun j => value_matrix.filterMap fun row => row[j]?)
    else back_err no_region "cannot transpose a matrix of value batches"

/-- Mirrors `sub_opt`: the sub-context of an optional iteration, `none`
when the iterated variables are all absent. -/
def sub_opt (ctx : t) (vars : List var) : backtrack (Option t) := do
  let values ← find_values ctx (vars.map fun v => (v.id, v.iters ++ [.Opt]))
  let values ← values.mapM fun v => Eval.err? (Value.Get.opt v)
  if values.all Option.isSome then
    let ctx_sub := (vars.zip values).foldl (fun ctx_sub (v, value) =>
      match value with
      | some value => add_value ctx_sub (v.id, v.iters) value
      | none => ctx_sub) ctx
    pure (some ctx_sub)
  else if values.all Option.isNone then pure none
  else back_err no_region "mismatch in optionality of iterated variables"

/-- Mirrors `sub_list`: one sub-context per batch of the iterated lists. -/
def sub_list (ctx : t) (vars : List var) : backtrack (List t) := do
  let values ← find_values ctx (vars.map fun v => (v.id, v.iters ++ [.List]))
  let values ← values.mapM fun v => Eval.err? (Value.Get.list v)
  let values_batch ← transpose values
  pure (values_batch.map fun value_batch =>
    (vars.zip value_batch).foldl (fun ctx_sub (v, value) => add_value ctx_sub (v.id, v.iters) value)
      ctx)

end P4SpecTec.Interp_al.Ctx
