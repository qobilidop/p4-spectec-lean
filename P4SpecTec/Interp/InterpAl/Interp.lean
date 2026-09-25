import P4SpecTec.Interp.InterpAl.Ctx
import P4SpecTec.Runtime.Value.Match
import P4SpecTec.Interface.Builtin.Call
import P4SpecTec.Lang.Hints.Input

/-!
The AL interpreter. Mirrors `p4spec/lib/interp/interp-al/interp.ml`,
TRUSTED (design section 5.2): the same functions in the same order, each
named as upstream, in the `Eval` monad of `Backtrack.lean`. Deviations,
listed in the design (section 5.3):

- Every function of the recursive block takes a fuel and consumes one
  unit per call; `none` (`Eval.diverge`) is exhaustion. The OCaml
  recurses freely.
- The interpreter is parameterised by `Config`: the extern
  implementations (the `Extern` functor argument) and the guard flag
  (`check_guard`); the `Interface` argument is the builtin dispatcher
  `Builtin.Call.invoke`. The caches, hooks, backtraces and the
  deterministic mode (`Nondet`) are not mirrored: they are instrumentation
  and checks, not meaning.
- Where the OCaml raises an exception or fails an assertion (a value of
  the wrong shape, `List.hd` of an empty list, an optionality mismatch),
  the result is `Fail.err`, the kind upstream never backtracks over.
- A `debug` premise prints nothing.
- Regions in messages are not kept; every message is dropped with its
  trace.
-/

namespace P4SpecTec.Interp_al.Interp

open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Xl
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al
open P4SpecTec.Prelude
open P4SpecTec.Runtime
open P4SpecTec.Runtime.Type
open P4SpecTec.Runtime.Dynamic
open P4SpecTec.Runtime.Dynamic_al
open P4SpecTec.Interp_al.Backtrack

/-- The extern implementations (the `Extern` functor argument): an extern
relation or function on values; a failure is a mismatch or an error. -/
structure Extern where
  /-- Mirrors `Extern.eval_extern_rel`. -/
  eval_extern_rel : String → List value → backtrack (List value)
  /-- Mirrors `Extern.eval_extern_func`. -/
  eval_extern_func : String → List typ → List value → backtrack value

/-- No externs: every extern call is undefined. -/
def Extern.none : Extern where
  eval_extern_rel := fun i _ => back_err no_region s!"extern relation {i} is undefined"
  eval_extern_func := fun i _ _ => back_err no_region s!"extern function {i} is undefined"

/-- The interpreter's configuration: the externs and the guard flag
(`check_guard`, on by default). -/
structure Config where
  /-- The extern implementations. -/
  extern : Extern := .none
  /-- Whether relation and function inputs and outputs are checked against
  their declared types at the entry points. -/
  guard : Bool := true
  /-- Whether every invocation and its outcome is traced on stderr
  (`dbgTrace`), for diagnosis. -/
  debug : Bool := false

/-- The outcome of an evaluation, for the trace. -/
def outcome {α : Type} (r : backtrack α) : String :=
  match r.run with
  | some (.ok _) => "ok"
  | some (.error .err) => "err"
  | some (.error .unmatch) => "unmatch"
  | none => "diverge"

/-- Trace an invocation when `debug` is set. -/
def traced {α : Type} (cfg : Config) (what : String) (r : backtrack α) : backtrack α :=
  if cfg.debug then dbgTrace s!"{what}: {outcome r}" fun _ => r else r

/-- `typ_note`: an expression's type as a typed phrase (`exp.note $ exp.at`). -/
def typ_note (e : exp) : typ := mkPhrase e.note e.at

/-- A type phrase from a value's note (`value.note.typ $ at`). -/
def typ_of_value (v : value) («at» : region) : typ := mkPhrase v.note.typ «at»

/-! Checkers -/

/-- Mirrors `check_rel_inputs`. -/
def check_rel_inputs (cfg : Config) (ctx : Ctx.t) (id_rel : Lang.Il.id)
    (values_input : List value) : backtrack Unit := do
  if !cfg.guard then return ()
  let (nottyp, inputs) ← Ctx.find_rel_signature ctx id_rel
  let typs := Mixfix.args nottyp.it
  let typs := inputs.filterMap fun i => typs[i.toNat]?
  check_back_err
    (Value.Match.subs (Ctx.find_typdef_opt' ctx) (Ctx.find_func_signature_opt' ctx) typs
      values_input)
    id_rel.at s!"relation input of {id_rel.it} does not match the expected type"

/-- Mirrors `check_rel_outputs`. -/
def check_rel_outputs (cfg : Config) (ctx : Ctx.t) (id_rel : Lang.Il.id) (nottyp : nottyp)
    (inputs : Lang.Il.Hints.Input.t) (values_output : List value) : backtrack Unit := do
  if !cfg.guard then return ()
  let typs := Mixfix.args nottyp.it
  let typs := typs.zipIdx.filterMap fun (typ, idx) =>
    if inputs.contains idx then none else some typ
  check_back_err
    (Value.Match.subs (Ctx.find_typdef_opt' ctx) (Ctx.find_func_signature_opt' ctx) typs
      values_output)
    id_rel.at s!"relation output of {id_rel.it} does not match the expected type"

/-- Mirrors `check_func_inputs`. -/
def check_func_inputs (cfg : Config) (ctx : Ctx.t) (id_func : Lang.Il.id) (targs : List targ)
    (values_input : List value) : backtrack Unit := do
  if !cfg.guard then return ()
  let (tparams, typs_params, _) ← Ctx.find_func_signature ctx id_func
  let ctx_local := Ctx.localize ctx
  check_back_err (targs.length == tparams.length) id_func.at
    s!"arity mismatch in type arguments of {id_func.it}"
  let ctx_local ← (tparams.zip targs).foldlM (fun ctx_local (tparam, targ) =>
    Ctx.add_typdef ctx_local tparam (.Defined [] (mkPhrase (.PlainT targ) targ.at))) ctx_local
  check_back_err
    (Value.Match.subs (Ctx.find_typdef_opt' ctx_local) (Ctx.find_func_signature_opt' ctx_local)
      typs_params values_input)
    id_func.at s!"function argument of {id_func.it} does not match the parameter type"

/-- Mirrors `check_func_output`. -/
def check_func_output (cfg : Config) (ctx : Ctx.t) (id_func : Lang.Il.id) (tparams : List tparam)
    (typ_output : typ) (targs : List targ) (value_output : value) : backtrack Unit := do
  if !cfg.guard then return ()
  let theta := Subst.of_lists tparams targs
  let typ_output := Subst.subst_typ theta typ_output
  check_back_err
    (Value.Match.sub (Ctx.find_typdef_opt' ctx) (Ctx.find_func_signature_opt' ctx) typ_output
      value_output)
    id_func.at s!"return value of function {id_func.it} does not match the expected type"

/-! Helper for checking if an expression is a simple iteration of a variable -/

/-- Mirrors `is_iter_var_exp`; recursion on the size of the expression,
since it descends through the phrase's payload. -/
def is_iter_var_exp (e : exp) : Option Var.t :=
  match _h : e.it with
  | .VarE id_exp => some (id_exp, [])
  | .IterE exp_inner iterexp =>
    match is_iter_var_exp exp_inner with
    | some (id_var, iters_var) =>
      match iterexp with
      | .mk iter [v] =>
        if id_var.it == v.id.it && iters_var == v.iters then some (id_var, iters_var ++ [iter])
        else none
      | _ => none
    | none => none
  | _ => none
termination_by sizeOf e
decreasing_by
  have h' : sizeOf e.it = sizeOf (exp'.IterE exp_inner iterexp) := by rw [_h]
  obtain ⟨it, note, «at»⟩ := e
  simp only [info.mk.sizeOf_spec, exp'.IterE.sizeOf_spec] at h' ⊢
  omega

/-! Assignments: the non-recursive cases -/

/-- Mirrors `assign_var_exp`. -/
def assign_var_exp (ctx : Ctx.t) (i : Lang.Il.id) (value : value) : backtrack Ctx.t :=
  pure (Ctx.add_value ctx (i, []) value)

/-- Mirrors `assign_arg_def`. -/
def assign_arg_def (ctx_caller ctx_callee : Ctx.t) (i : Lang.Il.id) (value : value) :
    backtrack Ctx.t := do
  match value.it with
  | .FuncV id_f =>
    let (_, func) ← Ctx.find_func ctx_caller id_f
    Ctx.add_func ctx_callee i func
  | _ => back_err i.at s!"cannot assign a value to a definition {i.it}"

/-! Expression evaluation: the non-recursive cases -/

/-- Mirrors `eval_bool_exp`. -/
def eval_bool_exp (_typ_note : typ) (b : Bool) : backtrack value := pure (Value.Make.bool b)

/-- Mirrors `eval_num_exp`. -/
def eval_num_exp (_typ_note : typ) (n : Num.t) : backtrack value := pure (Value.Make.num n)

/-- Mirrors `eval_text_exp`. -/
def eval_text_exp (_typ_note : typ) (s : String) : backtrack value := pure (Value.Make.text s)

/-- Mirrors `eval_var_exp`. -/
def eval_var_exp (_typ_note : typ) (ctx : Ctx.t) (i : Lang.Il.id) : backtrack value :=
  Ctx.find_value ctx (i, [])

/-- Mirrors `eval_un_bool`. -/
def eval_un_bool (_unop : unop) (v : value) : backtrack value := do
  pure (Value.Make.bool !(← Eval.err? (Value.Get.bool v)))

/-- Mirrors `eval_un_num`. -/
def eval_un_num (unop : Num.unop) (v : value) : backtrack value := do
  pure (Value.Make.num (Num.un unop (← Eval.err? (Value.Get.num v))))

/-- Mirrors `eval_bin_bool`. -/
def eval_bin_bool (binop : binop) (value_l value_r : value) : backtrack value := do
  let b_l ← Eval.err? (Value.Get.bool value_l)
  let b_r ← Eval.err? (Value.Get.bool value_r)
  match binop with
  | .AndOp => pure (Value.Make.bool (b_l && b_r))
  | .OrOp => pure (Value.Make.bool (b_l || b_r))
  | .ImplOp => pure (Value.Make.bool (!b_l || b_r))
  | .EquivOp => pure (Value.Make.bool (b_l == b_r))
  | _ => back_err no_region "not a boolean operator"

/-- Mirrors `eval_bin_num`. -/
def eval_bin_num (binop : Num.binop) (value_l value_r : value) : backtrack value := do
  let num_l ← Eval.err? (Value.Get.num value_l)
  let num_r ← Eval.err? (Value.Get.num value_r)
  pure (Value.Make.num (← Eval.err? (Num.bin binop num_l num_r)))

/-- Mirrors `eval_cmp_bool`. -/
def eval_cmp_bool (cmpop : cmpop) (value_l value_r : value) : backtrack value :=
  let eq := Value.eq value_l value_r
  match cmpop with
  | .EqOp => pure (Value.Make.bool eq)
  | .NeOp => pure (Value.Make.bool !eq)
  | _ => back_err no_region "not a boolean comparison"

/-- Mirrors `eval_cmp_num`. -/
def eval_cmp_num (cmpop : Num.cmpop) (value_l value_r : value) : backtrack value := do
  let num_l ← Eval.err? (Value.Get.num value_l)
  let num_r ← Eval.err? (Value.Get.num value_r)
  pure (Value.Make.bool (← Eval.err? (Num.cmp cmpop num_l num_r)))

/-- The `Num.binop` of a `binop`, if it is one. -/
def numBinop : binop → Option Num.binop
  | .AddOp => some .AddOp | .SubOp => some .SubOp | .MulOp => some .MulOp
  | .DivOp => some .DivOp | .ModOp => some .ModOp | .PowOp => some .PowOp
  | _ => none

/-- The `Num.cmpop` of a `cmpop`, if it is one. -/
def numCmpop : cmpop → Option Num.cmpop
  | .LtOp => some .LtOp | .GtOp => some .GtOp | .LeOp => some .LeOp | .GeOp => some .GeOp
  | _ => none

/-- Mirrors `eval_match_exp`'s test (`matches` is a Lean token). -/
def pattern_matches (pattern : pattern) (value : value) : Bool :=
  match pattern, value.it with
  | .CaseP mixop_p, .CaseV valuecase => Mixfix.eq_mixop mixop_p valuecase
  | .ListP listpattern, .ListV values =>
    let len_v := values.length
    match listpattern with
    | .Cons => len_v > 0
    | .Fixed len_p => len_v == len_p
    | .Nil => len_v == 0
  | .OptP .Some, .OptV (some _) => true
  | .OptP .None, .OptV none => true
  | _, _ => false

/-- Mirrors `eval_dot_exp`'s lookup: the field named by the atom. -/
def dot (valuefields : List valuefield) (atom : atom) : backtrack value :=
  match valuefields.find? fun (atom_field, _) => Atom.eq atom_field.it atom.it with
  | some (_, v) => pure v
  | none => back_err atom.at "no such field"

/-- An index from a number value (`Num.to_int |> Bigint.to_int_exn`). -/
def index_of (v : value) : backtrack Int := do pure (Num.to_int (← Eval.err? (Value.Get.num v)))

/-- Mirrors `eval_idx_exp`'s access, on a text or a list. -/
def index (value_b : value) (idx : Int) («at» : region) : backtrack value :=
  match value_b.it with
  | .TextV s =>
    if idx < 0 || idx ≥ s.length then back_err «at» "index out of bounds"
    else match s.toList[idx.toNat]? with
      | some c => pure (Value.Make.text (String.singleton c))
      | none => back_err «at» "index out of bounds"
  | .ListV values =>
    if idx < 0 || idx ≥ values.length then back_err «at» "index out of bounds"
    else match values[idx.toNat]? with
      | some v => pure v
      | none => back_err «at» "index out of bounds"
  | _ => back_err «at» "indexing expects either a text or a list"

/-- Mirrors `eval_slice_exp`'s access. -/
def slice (typ : typ) (value_b : value) (idx_l idx_n : Int) («at» : region) : backtrack value :=
  let idx_h := idx_l + idx_n
  match value_b.it with
  | .TextV s =>
    if idx_l < 0 || idx_h > s.length then back_err «at» "slice out of bounds"
    else pure (Value.Make.text (String.ofList ((s.toList.drop idx_l.toNat).take idx_n.toNat)))
  | .ListV values =>
    if idx_l < 0 || idx_h > values.length then back_err «at» "slice out of bounds"
    else pure (Value.Make.list typ.it ((values.drop idx_l.toNat).take idx_n.toNat))
  | _ => back_err «at» "slicing expects either a text or a list"

/-- Mirrors `eval_update_path`'s update of an index. -/
def update_index (typ : typ) (v : value) (idx_target : Int) (value_upd : value)
    («at» : region) : backtrack value :=
  match v.it with
  | .TextV s =>
    if idx_target < 0 || idx_target ≥ s.length then back_err «at» "index out of bounds"
    else do
      let s_n ← Eval.err? (Value.Get.text value_upd)
      if s_n.length != 1 then back_err «at» "updating a character requires a single-character text"
      else
        let cs := s.toList
        pure (Value.Make.text (String.ofList (cs.take idx_target.toNat ++ s_n.toList ++
          cs.drop (idx_target.toNat + 1))))
  | .ListV values =>
    if idx_target < 0 || idx_target ≥ values.length then back_err «at» "index out of bounds"
    else pure (Value.Make.list typ.it (values.set idx_target.toNat value_upd))
  | _ => back_err «at» "indexing expects either a text or a list"

/-- Mirrors `eval_update_path`'s update of a slice. -/
def update_slice (typ : typ) (v : value) (idx_l idx_n : Int) (value_upd : value)
    («at» : region) : backtrack value :=
  let idx_h := idx_l + idx_n
  match v.it with
  | .TextV s =>
    if idx_l < 0 || idx_h > s.length then back_err «at» "slice out of bounds"
    else do
      let s_upd ← Eval.err? (Value.Get.text value_upd)
      if s_upd.length != idx_n then back_err «at» "updating a slice requires a text of its length"
      else
        let cs := s.toList
        pure (Value.Make.text (String.ofList (cs.take idx_l.toNat ++ s_upd.toList ++
          cs.drop idx_h.toNat)))
  | .ListV values =>
    if idx_l < 0 || idx_h > values.length then back_err «at» "slice out of bounds"
    else do
      let values_upd ← Eval.err? (Value.Get.list value_upd)
      if values_upd.length != idx_n then
        back_err «at» "updating a slice requires a list of its length"
      else pure (Value.Make.list typ.it (values.take idx_l.toNat ++ values_upd ++
        values.drop idx_h.toNat))
  | _ => back_err «at» "slicing expects either a text or a list"

/-- Mirrors `eval_arg`'s `DefA` case. -/
def eval_arg_def (ctx : Ctx.t) (i : Lang.Il.id) : backtrack value := do
  let (tparams, typs, typ) ← Ctx.find_func_signature ctx i
  pure (Value.Make.func i tparams typs typ)

/-- Mirrors `eval_call_exp`'s substitution of type arguments through the
local type aliases. -/
def subst_targs (ctx : Ctx.t) (targs : List targ) : List targ :=
  match targs with
  | [] => []
  | targs =>
    let theta : Subst.theta := ctx.«local».tdenv.filterMap fun (tid, td) =>
      match td with
      | .Defined [] ⟨.PlainT typ, _, _⟩ => some (tid, typ)
      | _ => none
    targs.map (Subst.subst_typ theta)

/-! The recursive block: assignment, evaluation and invocation -/

mutual

/-- Mirrors `assign_exp`. -/
def assign_exp : Nat → Ctx.t → exp → value → backtrack Ctx.t
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, ctx, exp, value =>
    let typ_value := typ_of_value value exp.at
    match exp.it, value.it with
    | .VarE i, _ => assign_var_exp ctx i value
    | .TupleE exps, .TupleV values => assign_tuple_exp fuel ctx exps values
    | .CaseE notexp, .CaseV valuecase => assign_case_exp fuel ctx notexp valuecase
    | .StrE expfields, .StructV valuefields => assign_str_exp fuel ctx expfields valuefields
    | .OptE exp_opt, .OptV value_opt => assign_opt_exp fuel ctx exp_opt value_opt
    | .ListE exps, .ListV values => assign_list_exp fuel ctx exps values
    | .ConsE exp_h exp_t, .ListV values_inner =>
      assign_cons_exp fuel typ_value ctx exp_h exp_t values_inner
    | .IterE exp_inner iterexp, _ => assign_iter_exp fuel (typ_note exp) ctx exp_inner iterexp value
    | _, _ => back_err exp.at "match failed"

/-- Mirrors `assign_exps`. -/
def assign_exps : Nat → Ctx.t → List exp → List value → backtrack Ctx.t
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, ctx, exps, values => do
    check_back_err (exps.length == values.length) no_region
      "mismatch in number of expressions and values while assigning"
    (exps.zip values).foldlM (fun ctx (exp, value) => assign_exp fuel ctx exp value) ctx

/-- Mirrors `assign_tuple_exp`. -/
def assign_tuple_exp : Nat → Ctx.t → List exp → List value → backtrack Ctx.t
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, ctx, exps, values => assign_exps fuel ctx exps values

/-- Mirrors `assign_case_exp`. -/
def assign_case_exp : Nat → Ctx.t → notexp → valuecase → backtrack Ctx.t
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, ctx, notexp, valuecase =>
    assign_exps fuel ctx (Mixfix.args notexp) (Mixfix.args valuecase)

/-- Mirrors `assign_str_exp`. -/
def assign_str_exp : Nat → Ctx.t → List (atom × exp) → List (atom × value) → backtrack Ctx.t
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, ctx, expfields, valuefields =>
    assign_exps fuel ctx (expfields.map (·.2)) (valuefields.map (·.2))

/-- Mirrors `assign_opt_exp`. -/
def assign_opt_exp : Nat → Ctx.t → Option exp → Option value → backtrack Ctx.t
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, ctx, exp_opt, value_opt =>
    match exp_opt, value_opt with
    | some exp, some value => assign_exp fuel ctx exp value
    | none, none => pure ctx
    | _, _ => back_err no_region "optionality mismatch"

/-- Mirrors `assign_list_exp`. -/
def assign_list_exp : Nat → Ctx.t → List exp → List value → backtrack Ctx.t
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, ctx, exps, values => assign_exps fuel ctx exps values

/-- Mirrors `assign_cons_exp`. -/
def assign_cons_exp : Nat → typ → Ctx.t → exp → exp → List value → backtrack Ctx.t
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, typ_value, ctx, exp_h, exp_t, values =>
    match values with
    | [] => back_err exp_h.at "empty list"
    | value_h :: values_t => do
      let value_t := Value.Make.list typ_value.it values_t
      let ctx ← assign_exp fuel ctx exp_h value_h
      assign_exp fuel ctx exp_t value_t

/-- Mirrors `assign_iter_exp_opt`. -/
def assign_iter_exp_opt : Nat → Ctx.t → exp → List var → value → backtrack Ctx.t
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, ctx, exp, vars, value => do
    match ← Eval.err? (Value.Get.opt value) with
    | some inner_value =>
      let ctx ← assign_exp fuel ctx exp inner_value
      let inner_values ← Ctx.find_values ctx (vars.map fun v => (v.id, v.iters))
      pure ((vars.zip inner_values).foldl (fun ctx (v, inner_value) =>
        let typ := Typ.Make.iterate v.typ (v.iters ++ [.Opt])
        Ctx.add_value ctx (v.id, v.iters ++ [.Opt]) (Value.Make.opt typ.it (some inner_value))) ctx)
    | none =>
      pure (vars.foldl (fun ctx v =>
        let typ := Typ.Make.iterate v.typ (v.iters ++ [.Opt])
        Ctx.add_value ctx (v.id, v.iters ++ [.Opt]) (Value.Make.opt typ.it none)) ctx)

/-- Mirrors `assign_iter_exp_list`. -/
def assign_iter_exp_list : Nat → Ctx.t → exp → List var → value → backtrack Ctx.t
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, ctx, exp, vars, value => do
    let values ← Eval.err? (Value.Get.list value)
    let ctx_sub : Ctx.t := { ctx with «local» := { ctx.«local» with venv := [] } }
    let ctxs ← values.mapM fun value => assign_exp fuel ctx_sub exp value
    vars.foldlM (fun ctx v => do
      let typ := Typ.Make.iterate v.typ (v.iters ++ [.List])
      let values ← ctxs.mapM fun ctx' => Ctx.find_value ctx' (v.id, v.iters)
      pure (Ctx.add_value ctx (v.id, v.iters ++ [.List]) (Value.Make.list typ.it values))) ctx

/-- Mirrors `assign_iter_exp`. -/
def assign_iter_exp : Nat → typ → Ctx.t → exp → iterexp → value → backtrack Ctx.t
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, typ_exp, ctx, exp, iterexp, value =>
    match is_iter_var_exp ⟨.IterE exp iterexp, typ_exp.it, typ_exp.at⟩ with
    | some (id_var, iters_var) => pure (Ctx.add_value ctx (id_var, iters_var) value)
    | none =>
      match iterexp with
      | .mk .Opt vars => assign_iter_exp_opt fuel ctx exp vars value
      | .mk .List vars => assign_iter_exp_list fuel ctx exp vars value

/-- Mirrors `assign_arg`. -/
def assign_arg : Nat → Ctx.t → Ctx.t → arg → value → backtrack Ctx.t
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, ctx_caller, ctx_callee, arg, value =>
    match arg.it with
    | .ExpA exp => assign_arg_exp fuel ctx_callee exp value
    | .DefA i => assign_arg_def ctx_caller ctx_callee i value

/-- Mirrors `assign_args`. -/
def assign_args : Nat → Ctx.t → Ctx.t → List arg → List value → backtrack Ctx.t
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, ctx_caller, ctx_callee, args, values => do
    check_back_err (args.length == values.length) no_region
      "mismatch in number of arguments and values while assigning"
    (args.zip values).foldlM (fun ctx_callee (arg, value) =>
      assign_arg fuel ctx_caller ctx_callee arg value) ctx_callee

/-- Mirrors `assign_arg_exp`. -/
def assign_arg_exp : Nat → Ctx.t → exp → value → backtrack Ctx.t
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, ctx, exp, value => assign_exp fuel ctx exp value

/-- Mirrors `eval_exp`. -/
def eval_exp : Nat → Config → Ctx.t → exp → backtrack value
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, exp =>
    let typ_note := typ_note exp
    match exp.it with
    | .BoolE b => eval_bool_exp typ_note b
    | .NumE n => eval_num_exp typ_note n
    | .TextE s => eval_text_exp typ_note s
    | .VarE i => eval_var_exp typ_note ctx i
    | .UnE unop optyp exp => eval_un_exp fuel cfg typ_note ctx unop optyp exp
    | .BinE binop optyp exp_l exp_r => eval_bin_exp fuel cfg typ_note ctx binop optyp exp_l exp_r
    | .CmpE cmpop optyp exp_l exp_r => eval_cmp_exp fuel cfg typ_note ctx cmpop optyp exp_l exp_r
    | .UpCastE typ exp => eval_upcast_exp fuel cfg typ_note ctx typ exp
    | .DownCastE typ exp => eval_downcast_exp fuel cfg typ_note ctx typ exp
    | .SubE exp typ subcheck => eval_sub_exp fuel cfg typ_note ctx exp typ subcheck
    | .MatchE exp pattern => eval_match_exp fuel cfg typ_note ctx exp pattern
    | .TupleE exps => eval_tuple_exp fuel cfg typ_note ctx exps
    | .CaseE typ_notexp => eval_case_exp fuel cfg typ_note ctx typ_notexp
    | .StrE fields => eval_str_exp fuel cfg typ_note ctx fields
    | .OptE exp_opt => eval_opt_exp fuel cfg typ_note ctx exp_opt
    | .ListE exps => eval_list_exp fuel cfg typ_note ctx exps
    | .ConsE exp_h exp_t => eval_cons_exp fuel cfg typ_note ctx exp_h exp_t
    | .CatE exp_l exp_r => eval_cat_exp fuel cfg typ_note ctx exp_l exp_r
    | .MemE exp_e exp_s => eval_mem_exp fuel cfg typ_note ctx exp_e exp_s
    | .LenE exp => eval_len_exp fuel cfg typ_note ctx exp
    | .DotE exp_b atom => eval_dot_exp fuel cfg typ_note ctx exp_b atom
    | .IdxE exp_b exp_i => eval_idx_exp fuel cfg typ_note ctx exp_b exp_i
    | .SliceE exp_b exp_l exp_h => eval_slice_exp fuel cfg typ_note ctx exp_b exp_l exp_h
    | .UpdE exp_b path exp_f => eval_upd_exp fuel cfg typ_note ctx exp_b path exp_f
    | .CallE i targs args => eval_call_exp fuel cfg typ_note ctx i targs args
    | .IterE exp iterexp => eval_iter_exp fuel cfg typ_note ctx exp iterexp

/-- Mirrors `eval_exps`. -/
def eval_exps : Nat → Config → Ctx.t → List exp → backtrack (List value)
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, exps => exps.mapM fun exp => eval_exp fuel cfg ctx exp

/-- Mirrors `eval_un_exp`. -/
def eval_un_exp : Nat → Config → typ → Ctx.t → unop → optyp → exp → backtrack value
  | 0, _, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, _typ_note, ctx, unop, _optyp, exp => do
    let value ← eval_exp fuel cfg ctx exp
    match unop with
    | .NotOp => eval_un_bool unop value
    | .PlusOp => eval_un_num .PlusOp value
    | .MinusOp => eval_un_num .MinusOp value

/-- Mirrors `eval_bin_exp`. -/
def eval_bin_exp : Nat → Config → typ → Ctx.t → binop → optyp → exp → exp → backtrack value
  | 0, _, _, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, _typ_note, ctx, binop, _optyp, exp_l, exp_r => do
    let value_l ← eval_exp fuel cfg ctx exp_l
    let value_r ← eval_exp fuel cfg ctx exp_r
    match numBinop binop with
    | some binop => eval_bin_num binop value_l value_r
    | none => eval_bin_bool binop value_l value_r

/-- Mirrors `eval_cmp_exp`. -/
def eval_cmp_exp : Nat → Config → typ → Ctx.t → cmpop → optyp → exp → exp → backtrack value
  | 0, _, _, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, _typ_note, ctx, cmpop, _optyp, exp_l, exp_r => do
    let value_l ← eval_exp fuel cfg ctx exp_l
    let value_r ← eval_exp fuel cfg ctx exp_r
    match numCmpop cmpop with
    | some cmpop => eval_cmp_num cmpop value_l value_r
    | none => eval_cmp_bool cmpop value_l value_r

/-- Mirrors `upcast`. -/
def upcast : Nat → Ctx.t → typ → value → backtrack value
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, ctx, typ, value =>
    match typ.it with
    | .NumT .IntT =>
      match value.it with
      | .NumV (.Nat n) => pure (Value.Make.int n)
      | .NumV (.Int _) => pure value
      | _ => back_err typ.at "not a number"
    | .VarT tid targs => do
      let (tparams, deftyp) ← Ctx.find_defined_typdef ctx tid
      let theta := Subst.of_lists tparams targs
      match deftyp.it with
      | .PlainT typ => upcast fuel ctx (Subst.subst_typ theta typ) value
      | _ => pure value
    | .TupleT typs =>
      match value.it with
      | .TupleV values => do
        let values ← (typs.zip values).mapM fun (typ, value) => upcast fuel ctx typ value
        pure (Value.Make.tuple typ.it values)
      | _ => back_err typ.at "not a tuple"
    | .IterT typ' .Opt =>
      match value.it with
      | .OptV none => pure (Value.Make.opt typ'.it none)
      | .OptV (some value) => do
        pure (Value.Make.opt typ'.it (some (← upcast fuel ctx typ' value)))
      | _ => back_err typ.at "not an option"
    | .IterT typ' .List =>
      match value.it with
      | .ListV values => do
        pure (Value.Make.list typ'.it (← values.mapM fun value => upcast fuel ctx typ' value))
      | _ => back_err typ.at "not a list"
    | _ => pure value

/-- Mirrors `eval_upcast_exp`. -/
def eval_upcast_exp : Nat → Config → typ → Ctx.t → typ → exp → backtrack value
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, _typ_note, ctx, typ, exp => do
    upcast fuel ctx typ (← eval_exp fuel cfg ctx exp)

/-- Mirrors `downcast`. -/
def downcast : Nat → Ctx.t → typ → value → backtrack value
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, ctx, typ, value =>
    match typ.it with
    | .NumT .NatT =>
      match value.it with
      | .NumV (.Nat _) => pure value
      | .NumV (.Int i) =>
        if i ≥ 0 then pure (Value.Make.nat i.toNat) else back_err typ.at "negative"
      | _ => back_err typ.at "not a number"
    | .VarT tid targs => do
      let (tparams, deftyp) ← Ctx.find_defined_typdef ctx tid
      let theta := Subst.of_lists tparams targs
      match deftyp.it with
      | .PlainT typ => downcast fuel ctx (Subst.subst_typ theta typ) value
      | _ => pure value
    | .TupleT typs =>
      match value.it with
      | .TupleV values => do
        let values ← (typs.zip values).mapM fun (typ, value) => downcast fuel ctx typ value
        pure (Value.Make.tuple typ.it values)
      | _ => back_err typ.at "not a tuple"
    | .IterT typ' .Opt =>
      match value.it with
      | .OptV none => pure (Value.Make.opt typ'.it none)
      | .OptV (some value) => do
        pure (Value.Make.opt typ'.it (some (← downcast fuel ctx typ' value)))
      | _ => back_err typ.at "not an option"
    | .IterT typ' .List =>
      match value.it with
      | .ListV values => do
        pure (Value.Make.list typ'.it (← values.mapM fun value => downcast fuel ctx typ' value))
      | _ => back_err typ.at "not a list"
    | _ => pure value

/-- Mirrors `eval_downcast_exp`. -/
def eval_downcast_exp : Nat → Config → typ → Ctx.t → typ → exp → backtrack value
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, _typ_note, ctx, typ, exp => do
    downcast fuel ctx typ (← eval_exp fuel cfg ctx exp)

/-- Mirrors `eval_sub_exp`. -/
def eval_sub_exp : Nat → Config → typ → Ctx.t → exp → typ → subcheck → backtrack value
  | 0, _, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, _typ_note, ctx, exp, _typ, subcheck => do
    let value ← eval_exp fuel cfg ctx exp
    let sub := Value.Match.check (Ctx.find_typdef_opt' ctx) (Ctx.find_func_signature_opt' ctx)
      subcheck value
    pure (Value.Make.bool sub)

/-- Mirrors `eval_match_exp`. -/
def eval_match_exp : Nat → Config → typ → Ctx.t → exp → pattern → backtrack value
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, _typ_note, ctx, exp, pattern => do
    let value ← eval_exp fuel cfg ctx exp
    pure (Value.Make.bool (pattern_matches pattern value))

/-- Mirrors `eval_tuple_exp`. -/
def eval_tuple_exp : Nat → Config → typ → Ctx.t → List exp → backtrack value
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, typ_note, ctx, exps => do
    pure (Value.Make.tuple typ_note.it (← eval_exps fuel cfg ctx exps))

/-- Mirrors `eval_case_exp`. -/
def eval_case_exp : Nat → Config → typ → Ctx.t → notexp → backtrack value
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, typ_note, ctx, notexp => do
    let mixop := Mixfix.to_mixop notexp
    let values ← eval_exps fuel cfg ctx (Mixfix.args notexp)
    match Mixfix.fill mixop values with
    | some valuecase => pure (Value.Make.case typ_note.it valuecase)
    | none => back_err typ_note.at "arity mismatch"

/-- Mirrors `eval_str_exp`. -/
def eval_str_exp : Nat → Config → typ → Ctx.t → List (atom × exp) → backtrack value
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, typ_note, ctx, fields => do
    let values ← eval_exps fuel cfg ctx (fields.map (·.2))
    pure (Value.Make.mk typ_note.it (.StructV ((fields.map (·.1)).zip values)))

/-- Mirrors `eval_opt_exp`. -/
def eval_opt_exp : Nat → Config → typ → Ctx.t → Option exp → backtrack value
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, typ_note, ctx, exp_opt => do
    match exp_opt with
    | some exp => pure (Value.Make.opt typ_note.it (some (← eval_exp fuel cfg ctx exp)))
    | none => pure (Value.Make.opt typ_note.it none)

/-- Mirrors `eval_list_exp`. -/
def eval_list_exp : Nat → Config → typ → Ctx.t → List exp → backtrack value
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, typ_note, ctx, exps => do
    pure (Value.Make.list typ_note.it (← eval_exps fuel cfg ctx exps))

/-- Mirrors `eval_cons_exp`. -/
def eval_cons_exp : Nat → Config → typ → Ctx.t → exp → exp → backtrack value
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, typ_note, ctx, exp_h, exp_t => do
    let value_h ← eval_exp fuel cfg ctx exp_h
    let value_t ← eval_exp fuel cfg ctx exp_t
    let values_t ← Eval.err? (Value.Get.list value_t)
    pure (Value.Make.list typ_note.it (value_h :: values_t))

/-- Mirrors `eval_cat_exp`. -/
def eval_cat_exp : Nat → Config → typ → Ctx.t → exp → exp → backtrack value
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, typ_note, ctx, exp_l, exp_r => do
    let value_l ← eval_exp fuel cfg ctx exp_l
    let value_r ← eval_exp fuel cfg ctx exp_r
    match value_l.it, value_r.it with
    | .TextV s_l, .TextV s_r => pure (Value.Make.text (s_l ++ s_r))
    | .ListV values_l, .ListV values_r => pure (Value.Make.list typ_note.it (values_l ++ values_r))
    | _, _ => back_err typ_note.at "concatenation expects either two texts or two lists"

/-- Mirrors `eval_mem_exp`. -/
def eval_mem_exp : Nat → Config → typ → Ctx.t → exp → exp → backtrack value
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, _typ_note, ctx, exp_e, exp_s => do
    let value_e ← eval_exp fuel cfg ctx exp_e
    let value_s ← eval_exp fuel cfg ctx exp_s
    let values_s ← Eval.err? (Value.Get.list value_s)
    pure (Value.Make.bool (values_s.any (Value.eq value_e)))

/-- Mirrors `eval_len_exp`. -/
def eval_len_exp : Nat → Config → typ → Ctx.t → exp → backtrack value
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, _typ_note, ctx, exp => do
    let value ← eval_exp fuel cfg ctx exp
    match value.it with
    | .TextV s => pure (Value.Make.nat s.length)
    | .ListV values => pure (Value.Make.nat values.length)
    | _ => back_err exp.at "length operation expects either a text or a list"

/-- Mirrors `eval_dot_exp`. -/
def eval_dot_exp : Nat → Config → typ → Ctx.t → exp → atom → backtrack value
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, _typ_note, ctx, exp_b, atom => do
    let value_b ← eval_exp fuel cfg ctx exp_b
    dot (← Eval.err? (Value.Get.str value_b)) atom

/-- Mirrors `eval_idx_exp`. -/
def eval_idx_exp : Nat → Config → typ → Ctx.t → exp → exp → backtrack value
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, _typ_note, ctx, exp_b, exp_i => do
    let value_b ← eval_exp fuel cfg ctx exp_b
    let value_i ← eval_exp fuel cfg ctx exp_i
    index value_b (← index_of value_i) exp_i.at

/-- Mirrors `eval_slice_exp`. -/
def eval_slice_exp : Nat → Config → typ → Ctx.t → exp → exp → exp → backtrack value
  | 0, _, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, typ_note, ctx, exp_b, exp_i, exp_n => do
    let value_b ← eval_exp fuel cfg ctx exp_b
    let value_i ← eval_exp fuel cfg ctx exp_i
    let idx_l ← index_of value_i
    let value_n ← eval_exp fuel cfg ctx exp_n
    let idx_n ← index_of value_n
    slice typ_note value_b idx_l idx_n exp_i.at

/-- Mirrors `eval_access_path`. -/
def eval_access_path : Nat → Config → Ctx.t → value → path → backtrack value
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, value_b, path =>
    match path.it with
    | .RootP => pure value_b
    | .IdxP path exp_i => do
      let value ← eval_access_path fuel cfg ctx value_b path
      let value_i ← eval_exp fuel cfg ctx exp_i
      index value (← index_of value_i) exp_i.at
    | .SliceP path exp_i exp_n => do
      let typ : typ := mkPhrase path.note path.at
      let value ← eval_access_path fuel cfg ctx value_b path
      let value_i ← eval_exp fuel cfg ctx exp_i
      let idx_l ← index_of value_i
      let value_n ← eval_exp fuel cfg ctx exp_n
      let idx_n ← index_of value_n
      slice typ value idx_l idx_n exp_n.at
    | .DotP path atom => do
      let value ← eval_access_path fuel cfg ctx value_b path
      dot (← Eval.err? (Value.Get.str value)) atom

/-- Mirrors `eval_update_path`. -/
def eval_update_path : Nat → Config → Ctx.t → value → path → value → backtrack value
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, value_b, path, value_upd =>
    match path.it with
    | .RootP => pure value_upd
    | .IdxP path exp_i => do
      let typ : typ := mkPhrase path.note path.at
      let value ← eval_access_path fuel cfg ctx value_b path
      let value_i ← eval_exp fuel cfg ctx exp_i
      let idx_target ← index_of value_i
      let value ← update_index typ value idx_target value_upd exp_i.at
      eval_update_path fuel cfg ctx value_b path value
    | .SliceP path exp_i exp_n => do
      let typ : typ := mkPhrase path.note path.at
      let value ← eval_access_path fuel cfg ctx value_b path
      let value_i ← eval_exp fuel cfg ctx exp_i
      let idx_l ← index_of value_i
      let value_n ← eval_exp fuel cfg ctx exp_n
      let idx_n ← index_of value_n
      let value ← update_slice typ value idx_l idx_n value_upd exp_n.at
      eval_update_path fuel cfg ctx value_b path value
    | .DotP path atom => do
      let typ : typ := mkPhrase path.note path.at
      let value ← eval_access_path fuel cfg ctx value_b path
      let valuefields ← Eval.err? (Value.Get.str value)
      let valuefields := valuefields.map fun (atom_f, value_f) =>
        if Atom.eq atom_f.it atom.it then (atom_f, value_upd) else (atom_f, value_f)
      let value := Value.Make.mk typ.it (.StructV valuefields)
      eval_update_path fuel cfg ctx value_b path value

/-- Mirrors `eval_upd_exp`. -/
def eval_upd_exp : Nat → Config → typ → Ctx.t → exp → path → exp → backtrack value
  | 0, _, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, _typ_note, ctx, exp_b, path, exp_f => do
    let value_b ← eval_exp fuel cfg ctx exp_b
    let value_f ← eval_exp fuel cfg ctx exp_f
    eval_update_path fuel cfg ctx value_b path value_f

/-- Mirrors `eval_call_exp`. -/
def eval_call_exp : Nat → Config → typ → Ctx.t → Lang.Il.id → List targ → List arg →
    backtrack value
  | 0, _, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, _typ_note, ctx, i, targs, args => do
    let targs := subst_targs ctx targs
    let values_args ← eval_args fuel cfg ctx args
    invoke_func fuel cfg true ctx i targs values_args

/-- Mirrors `eval_iter_exp_opt`. -/
def eval_iter_exp_opt : Nat → Config → typ → Ctx.t → exp → List var → backtrack value
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, typ_note, ctx, exp, vars => do
    match ← Ctx.sub_opt ctx vars with
    | some ctx_sub => pure (Value.Make.opt typ_note.it (some (← eval_exp fuel cfg ctx_sub exp)))
    | none => pure (Value.Make.opt typ_note.it none)

/-- Mirrors `eval_iter_exp_list`. -/
def eval_iter_exp_list : Nat → Config → typ → Ctx.t → exp → List var → backtrack value
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, typ_note, ctx, exp, vars => do
    let ctxs_sub ← Ctx.sub_list ctx vars
    let values ← ctxs_sub.mapM fun ctx_sub => eval_exp fuel cfg ctx_sub exp
    pure (Value.Make.list typ_note.it values)

/-- Mirrors `eval_iter_exp`. -/
def eval_iter_exp : Nat → Config → typ → Ctx.t → exp → iterexp → backtrack value
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, typ_note, ctx, exp, iterexp =>
    match is_iter_var_exp ⟨.IterE exp iterexp, typ_note.it, typ_note.at⟩ with
    | some var => Ctx.find_value ctx var
    | none =>
      match iterexp with
      | .mk .Opt vars => eval_iter_exp_opt fuel cfg typ_note ctx exp vars
      | .mk .List vars => eval_iter_exp_list fuel cfg typ_note ctx exp vars

/-- Mirrors `eval_arg`. -/
def eval_arg : Nat → Config → Ctx.t → arg → backtrack value
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, arg =>
    match arg.it with
    | .ExpA exp => eval_exp fuel cfg ctx exp
    | .DefA i => eval_arg_def ctx i

/-- Mirrors `eval_args`. -/
def eval_args : Nat → Config → Ctx.t → List arg → backtrack (List value)
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, args => args.mapM fun arg => eval_arg fuel cfg ctx arg

/-- Mirrors `eval_prem` (and `eval_prem'`). -/
def eval_prem : Nat → Config → Ctx.t → prem → backtrack Ctx.t
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, prem =>
    match prem.it with
    | .RulePr i notexp inputs => eval_rule_prem fuel cfg ctx i notexp inputs
    | .IfPr exp_cond => eval_if_prem fuel cfg ctx exp_cond
    | .IfHoldPr i notexp => eval_if_hold_prem fuel cfg ctx i notexp
    | .IfNotHoldPr i notexp => eval_if_not_hold_prem fuel cfg ctx i notexp
    | .LetPr exp_l exp_r => eval_let_prem fuel cfg ctx exp_l exp_r
    | .IterPr prem iterprem => eval_iter_prem fuel cfg ctx prem iterprem
    | .DebugPr exp => eval_debug_prem fuel cfg ctx exp

/-- Mirrors `eval_prems`. -/
def eval_prems : Nat → Config → Ctx.t → List prem → backtrack Ctx.t
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, prems => prems.foldlM (fun ctx prem => eval_prem fuel cfg ctx prem) ctx

/-- Mirrors `eval_rule_prem`. -/
def eval_rule_prem : Nat → Config → Ctx.t → Lang.Il.id → notexp → Lang.Il.Hints.Input.t →
    backtrack Ctx.t
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, i, notexp, inputs => do
    let exps := Mixfix.args notexp
    let (exps_input, exps_output) := Lang.Hints.Input.split inputs exps
    let values_input ← eval_exps fuel cfg ctx exps_input
    let values_output ← invoke_rel fuel cfg true ctx i values_input
    assign_exps fuel ctx exps_output values_output

/-- Mirrors `eval_if_prem`. -/
def eval_if_prem : Nat → Config → Ctx.t → exp → backtrack Ctx.t
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, exp_cond => do
    let value_cond ← eval_exp fuel cfg ctx exp_cond
    let cond ← Eval.err? (Value.Get.bool value_cond)
    if cond then pure ctx else back_unmatch exp_cond.at "condition was not met"

/-- Mirrors `eval_if_hold_prem`. -/
def eval_if_hold_prem : Nat → Config → Ctx.t → Lang.Il.id → notexp → backtrack Ctx.t
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, i, notexp => do
    let values_input ← eval_exps fuel cfg ctx (Mixfix.args notexp)
    let _ ← invoke_rel fuel cfg true ctx i values_input
    pure ctx

/-- Mirrors `eval_if_not_hold_prem`. -/
def eval_if_not_hold_prem : Nat → Config → Ctx.t → Lang.Il.id → notexp → backtrack Ctx.t
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, i, notexp => do
    let values_input ← eval_exps fuel cfg ctx (Mixfix.args notexp)
    let _ ← Eval.notHold (invoke_rel fuel cfg true ctx i values_input)
    pure ctx

/-- Mirrors `eval_let_prem`. -/
def eval_let_prem : Nat → Config → Ctx.t → exp → exp → backtrack Ctx.t
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, exp_l, exp_r => do
    let value ← eval_exp fuel cfg ctx exp_r
    assign_exp fuel ctx exp_l value

/-- Mirrors `eval_iter_prem_opt`. -/
def eval_iter_prem_opt : Nat → Config → Ctx.t → prem → List var → List var → backtrack Ctx.t
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, prem, vars_bound, vars_bind => do
    match ← Ctx.sub_opt ctx vars_bound with
    | none =>
      pure (vars_bind.foldl (fun ctx v =>
        let typ := Typ.Make.iterate v.typ (v.iters ++ [.Opt])
        Ctx.add_value ctx (v.id, v.iters ++ [.Opt]) (Value.Make.opt typ.it none)) ctx)
    | some ctx_sub =>
      let ctx_sub ← eval_prem fuel cfg ctx_sub prem
      let values_binding ← Ctx.find_values ctx_sub (vars_bind.map fun v => (v.id, v.iters))
      pure ((vars_bind.zip values_binding).foldl (fun ctx (v, value_binding) =>
        let typ := Typ.Make.iterate v.typ (v.iters ++ [.Opt])
        Ctx.add_value ctx (v.id, v.iters ++ [.Opt]) (Value.Make.opt typ.it (some value_binding)))
        ctx)

/-- Mirrors `eval_iter_prem_list`. -/
def eval_iter_prem_list : Nat → Config → Ctx.t → prem → List var → List var → backtrack Ctx.t
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, prem, vars_bound, vars_bind => do
    let ctxs_sub ← Ctx.sub_list ctx vars_bound
    let values_binding ← match ctxs_sub with
      | [] => pure (vars_bind.map fun _ => [])
      | _ => do
        let values_binding_batch ← ctxs_sub.mapM fun ctx_sub => do
          let ctx_sub ← eval_prem fuel cfg ctx_sub prem
          Ctx.find_values ctx_sub (vars_bind.map fun v => (v.id, v.iters))
        Ctx.transpose values_binding_batch
    pure ((vars_bind.zip values_binding).foldl (fun ctx (v, values_binding) =>
      let typ := Typ.Make.iterate v.typ (v.iters ++ [.List])
      Ctx.add_value ctx (v.id, v.iters ++ [.List]) (Value.Make.list typ.it values_binding)) ctx)

/-- Mirrors `eval_iter_prem`. -/
def eval_iter_prem : Nat → Config → Ctx.t → prem → iterprem → backtrack Ctx.t
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, prem, iterprem =>
    match iterprem with
    | .mk .Opt vars_bound vars_bind => eval_iter_prem_opt fuel cfg ctx prem vars_bound vars_bind
    | .mk .List vars_bound vars_bind => eval_iter_prem_list fuel cfg ctx prem vars_bound vars_bind

/-- Mirrors `eval_debug_prem`: evaluates, prints nothing (deviation). -/
def eval_debug_prem : Nat → Config → Ctx.t → exp → backtrack Ctx.t
  | 0, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, exp => do
    let _ ← eval_exp fuel cfg ctx exp
    pure ctx

/-- Mirrors `match_rule`. -/
def match_rule : Nat → Ctx.t → region → rulematch → List value → backtrack (Ctx.t × List prem)
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, ctx, «at», rulematch, values_input => do
    let (_, exps_input, prems_input) := rulematch
    check_back_err (exps_input.length == values_input.length) «at» "arity mismatch in rule"
    let ctx ← assign_exps fuel ctx exps_input values_input
    pure (ctx, prems_input)

/-- Mirrors `invoke_rel`, without the cache and hooks; `internal` says
whether the inputs are already known to be well-typed. -/
def invoke_rel : Nat → Config → Bool → Ctx.t → Lang.Il.id → List value → backtrack (List value)
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, internal, ctx, i, values_input => traced cfg s!"relation {i.it}" do
    let rel ← Ctx.find_rel ctx i
    if !internal then check_rel_inputs cfg ctx i values_input
    match rel with
    | .Extern nottyp inputs => invoke_extern_rel fuel cfg ctx i nottyp inputs values_input
    | .Defined _ _ rulegroups elsegroup_opt =>
      invoke_defined_rel fuel cfg ctx i rulegroups elsegroup_opt values_input

/-- Mirrors `invoke_extern_rel`. -/
def invoke_extern_rel : Nat → Config → Ctx.t → Lang.Il.id → nottyp → Lang.Il.Hints.Input.t →
    List value → backtrack (List value)
  | 0, _, _, _, _, _, _ => Eval.diverge
  | _ + 1, cfg, ctx, i, nottyp, inputs, values_input => do
    let values_output ← cfg.extern.eval_extern_rel i.it values_input
    check_rel_outputs cfg ctx i nottyp inputs values_output
    pure values_output

/-- Mirrors `invoke_defined_rel`, sequential mode: the rule paths in
order, then the `else` group when none matched. -/
def invoke_defined_rel : Nat → Config → Ctx.t → Lang.Il.id → List Lang.Al.rulegroup →
    Option Lang.Al.elsegroup → List value → backtrack (List value)
  | 0, _, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, _id, rulegroups, elsegroup_opt, values_input =>
    let do_backtrack_rulepath (rulematch : rulematch) (rulepath : rulepath) :
        Unit → backtrack (List value) := fun _ => do
      let (id_rulepath, prems, exps_output) := rulepath
      let ctx_local := Ctx.localize ctx
      let (ctx_local, prems_input) ← match_rule fuel ctx_local id_rulepath.at rulematch values_input
      let ctx_local ← eval_prems fuel cfg ctx_local (prems_input ++ prems)
      eval_exps fuel cfg ctx_local exps_output
    let backtracks_path := rulegroups.flatMap fun rulegroup =>
      let (_, rulematch, rulepaths) := rulegroup.it
      rulepaths.map (do_backtrack_rulepath rulematch)
    Eval.orElse (choose_sequential backtracks_path)
      (match elsegroup_opt with
        | some eg =>
          let (_, rulematch, rulepath) := eg.it
          do_backtrack_rulepath rulematch rulepath ()
        | none => back_unmatch_silent)

/-- Mirrors `invoke_func`, without the cache and hooks. -/
def invoke_func : Nat → Config → Bool → Ctx.t → Lang.Il.id → List targ → List value →
    backtrack value
  | 0, _, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, internal, ctx, i, targs, values_input => traced cfg s!"function {i.it}" do
    let (_, func) ← Ctx.find_func ctx i
    if !internal then check_func_inputs cfg ctx i targs values_input
    invoke_func_body fuel cfg ctx i func targs values_input

/-- Mirrors `invoke_func_body`. -/
def invoke_func_body : Nat → Config → Ctx.t → Lang.Il.id → Func.t → List targ → List value →
    backtrack value
  | 0, _, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, i, func, targs, values_input =>
    match func with
    | .Extern tparams _ typ => invoke_extern_func fuel cfg ctx i tparams targs values_input typ
    | .Builtin tparams _ typ => invoke_builtin_func fuel cfg ctx i tparams targs values_input typ
    | .Table _ _ tablerows => invoke_table_func fuel cfg ctx i tablerows values_input
    | .Defined tparams _ _ clauses elseclause_opt =>
      invoke_defined_func fuel cfg ctx i tparams clauses elseclause_opt targs values_input

/-- Mirrors `invoke_extern_func`. -/
def invoke_extern_func : Nat → Config → Ctx.t → Lang.Il.id → List tparam → List targ →
    List value → typ → backtrack value
  | 0, _, _, _, _, _, _, _ => Eval.diverge
  | _ + 1, cfg, ctx, i, tparams, targs, values_input, typ_output => do
    let value_output ← cfg.extern.eval_extern_func i.it [] values_input
    check_func_output cfg ctx i tparams typ_output targs value_output
    pure value_output

/-- Mirrors `invoke_builtin_func`: a `BuiltinError` is a mismatch. -/
def invoke_builtin_func : Nat → Config → Ctx.t → Lang.Il.id → List tparam → List targ →
    List value → typ → backtrack value
  | 0, _, _, _, _, _, _, _ => Eval.diverge
  | _ + 1, cfg, ctx, i, tparams, targs, values_input, typ_output => do
    match Builtin.Call.invoke i.it targs values_input with
    | some value_output =>
      check_func_output cfg ctx i tparams typ_output targs value_output
      pure value_output
    | none => back_unmatch i.at s!"builtin {i.it} failed"

/-- Mirrors `match_tablerow`. -/
def match_tablerow : Nat → Ctx.t → Ctx.t → Lang.Al.tablerow → List value →
    backtrack (Ctx.t × List arg × List prem × exp)
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, ctx_caller, ctx_callee, row, values_input => do
    let (_, args_input, exp_output, prems) := row.it
    check_back_err (args_input.length == values_input.length) row.at
      "arity mismatch while matching table row"
    let ctx ← assign_args fuel ctx_caller ctx_callee args_input values_input
    pure (ctx, args_input, prems, exp_output)

/-- Mirrors `invoke_table_func`. -/
def invoke_table_func : Nat → Config → Ctx.t → Lang.Il.id → List Lang.Al.tablerow → List value →
    backtrack value
  | 0, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, _id, tablerows, values_input =>
    choose_sequential (tablerows.map fun row => fun _ => do
      let ctx_local := Ctx.localize ctx
      let (ctx_local, _, prems, exp_output) ← match_tablerow fuel ctx ctx_local row values_input
      let ctx_local ← eval_prems fuel cfg ctx_local prems
      eval_exp fuel cfg ctx_local exp_output)

/-- Mirrors `match_clause`. -/
def match_clause : Nat → Ctx.t → Ctx.t → clause → List value →
    backtrack (Ctx.t × List arg × List prem × exp)
  | 0, _, _, _, _ => Eval.diverge
  | fuel + 1, ctx_caller, ctx_callee, clause, values_input => do
    let (args_input, exp_output, prems) := clause.it
    check_back_err (args_input.length == values_input.length) clause.at
      "arity mismatch while matching clause"
    let ctx ← assign_args fuel ctx_caller ctx_callee args_input values_input
    pure (ctx, args_input, prems, exp_output)

/-- Mirrors `invoke_defined_func`, sequential mode: the clauses in order,
then the `else` clause when none matched. -/
def invoke_defined_func : Nat → Config → Ctx.t → Lang.Il.id → List tparam → List clause →
    Option elseclause → List targ → List value → backtrack value
  | 0, _, _, _, _, _, _, _, _ => Eval.diverge
  | fuel + 1, cfg, ctx, i, tparams, clauses, elseclause_opt, targs, values_input =>
    let do_backtrack_clause (clause : clause) : Unit → backtrack value := fun _ => do
      let ctx_local := Ctx.localize ctx
      check_back_err (targs.length == tparams.length) i.at "arity mismatch in type arguments"
      let ctx_local ← (tparams.zip targs).foldlM (fun ctx_local (tparam, targ) =>
        Ctx.add_typdef ctx_local tparam (.Defined [] (mkPhrase (.PlainT targ) targ.at))) ctx_local
      let (ctx_local, _, prems, exp_output) ← match_clause fuel ctx ctx_local clause values_input
      let ctx_local ← eval_prems fuel cfg ctx_local prems
      eval_exp fuel cfg ctx_local exp_output
    Eval.orElse (choose_sequential (clauses.map do_backtrack_clause))
      (match elseclause_opt with
        | some elseclause => do_backtrack_clause elseclause ()
        | none => back_unmatch_silent)

end

/-! Entry points for evaluation -/

/-- Mirrors `do_eval_rel`. -/
def do_eval_rel (fuel : Nat) (cfg : Config) (g : Ctx.global) (relname : String)
    (values_input : List value) : backtrack (List value) :=
  invoke_rel fuel cfg false (Ctx.empty g) (mkPhrase relname) values_input

/-- Mirrors `do_eval_func`. -/
def do_eval_func (fuel : Nat) (cfg : Config) (g : Ctx.global) (funcname : String)
    (targs : List targ) (values_input : List value) : backtrack value :=
  invoke_func fuel cfg false (Ctx.empty g) (mkPhrase funcname) targs values_input

/-- Mirrors `eval_rel`: the result as data (`Run.rel_result`). -/
def eval_rel (fuel : Nat) (cfg : Config) (g : Ctx.global) (relname : String)
    (values_input : List value) : Option (Except Fail (List value)) :=
  (do_eval_rel fuel cfg g relname values_input).run

/-- Mirrors `eval_func`. -/
def eval_func (fuel : Nat) (cfg : Config) (g : Ctx.global) (funcname : String) (targs : List targ)
    (values_input : List value) : Option (Except Fail value) :=
  (do_eval_func fuel cfg g funcname targs values_input).run

/-- Mirrors `init`: the global tables of a spec. -/
def init (spec : Lang.Al.spec) : Except String Ctx.global := Ctx.init spec

end P4SpecTec.Interp_al.Interp
