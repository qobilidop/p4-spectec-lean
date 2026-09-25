import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Split
import Lean.Elab.Tactic.RCases
import Lean.Elab.Tactic.Generalize
import Lean.Elab.Tactic.Omega.Frontend
import Lean.Meta.Eqns
import Lean.Meta.Match.MatcherApp.Basic
import P4SpecTec.Prelude
import P4SpecTec.Refine.Calc
import P4SpecTec.Tactic.RunSound

/-!
The tactic `refine_al` that discharges the generated refinement theorems
(design section 5.1, rung 3): the AL interpreter run on the quoted
definition refines the generated code. It is a lockstep symbolic
execution. The interpreter side is computed by `simp` with the
interpreter's own equations on the concrete quoted syntax, one fuel
level at a time (`cases` on the fuel; exhaustion refines anything); the
generated side is walked by the rules of `Refine/Calc.lean`: a `have`
binds its variable, a call of another definition is matched with the
interpreter's invocation through that definition's refinement theorem
(or the induction hypothesis inside a recursion group), an `if`
premise, a pattern match and a sequential choice are split on both
sides, and at a `pure` the results are related by computing `canon` on
both. The interpreter's values are related to the generated values by
facts `canon v = canon (toValue x)`; when the interpreter inspects a
value whose generated counterpart is a variable, that variable is
split by `cases`, which is the case analysis the generated code performs
too.

The tactic is generic: it knows nothing but the shapes the runtime,
the interpreter and the code generator fix, so a definition it cannot
close fails the build, which is what makes the generated theorem a check.
-/

namespace P4SpecTec.Tactic

open Lean Elab Tactic Meta
open P4SpecTec.Refine
open P4SpecTec.Interp_al

/-- Tracing for the driver. -/
register_option refine_al.trace : Bool := {
  defValue := false
  descr := "trace the steps of refine_al"
}

/-- Print a trace message when tracing is on: straight to stderr, so that a
failing step does not discard it with its state. -/
def traceStep (msg : MessageData) : TacticM Unit := do
  if refine_al.trace.get (← getOptions) then
    IO.eprintln s!"[refine_al] {← msg.toString}"

/-- Accumulated time per phase, in milliseconds, for the trace. -/
initialize phaseTimes : IO.Ref (List (String × Nat)) ← IO.mkRef []

/-- The action in progress, for error reports. -/
initialize phaseNow : IO.Ref String ← IO.mkRef ""

/-- Note the action in progress. -/
def noteAction (s : String) : TacticM Unit := phaseNow.set s

/-- Run a phase, accumulating its time. -/
def timed {α : Type} (label : String) (act : TacticM α) : TacticM α := do
  let t0 ← IO.monoMsNow
  try act
  finally
    let t1 ← IO.monoMsNow
    phaseTimes.modify fun l =>
      match l.lookup label with
      | some n => (label, n + (t1 - t0)) :: l.filter (·.1 != label)
      | none => (label, t1 - t0) :: l

/-! ## The simp sets -/

/-- The functions of the interpreter's recursive block, unfolded by their
equations (which fire only on a successor fuel). -/
def blockFunctions : List Name := [
  ``Interp.assign_exp, ``Interp.assign_exps, ``Interp.assign_tuple_exp, ``Interp.assign_case_exp,
  ``Interp.assign_str_exp, ``Interp.assign_opt_exp, ``Interp.assign_list_exp,
  ``Interp.assign_cons_exp, ``Interp.assign_iter_exp_opt, ``Interp.assign_iter_exp_list,
  ``Interp.assign_iter_exp, ``Interp.assign_arg, ``Interp.assign_args, ``Interp.assign_arg_exp,
  ``Interp.eval_exp, ``Interp.eval_exps, ``Interp.eval_un_exp, ``Interp.eval_bin_exp,
  ``Interp.eval_cmp_exp, ``Interp.upcast, ``Interp.eval_upcast_exp, ``Interp.downcast,
  ``Interp.eval_downcast_exp, ``Interp.eval_sub_exp, ``Interp.eval_match_exp,
  ``Interp.eval_tuple_exp, ``Interp.eval_case_exp, ``Interp.eval_str_exp, ``Interp.eval_opt_exp,
  ``Interp.eval_list_exp, ``Interp.eval_cons_exp, ``Interp.eval_cat_exp, ``Interp.eval_mem_exp,
  ``Interp.eval_len_exp, ``Interp.eval_dot_exp, ``Interp.eval_idx_exp, ``Interp.eval_slice_exp,
  ``Interp.eval_access_path, ``Interp.eval_update_path, ``Interp.eval_upd_exp,
  ``Interp.eval_call_exp, ``Interp.eval_iter_exp_opt, ``Interp.eval_iter_exp_list,
  ``Interp.eval_iter_exp, ``Interp.eval_arg, ``Interp.eval_args, ``Interp.eval_prem,
  ``Interp.eval_prems, ``Interp.eval_rule_prem, ``Interp.eval_if_prem, ``Interp.eval_if_hold_prem,
  ``Interp.eval_if_not_hold_prem, ``Interp.eval_let_prem, ``Interp.eval_iter_prem_opt,
  ``Interp.eval_iter_prem_list, ``Interp.eval_iter_prem, ``Interp.eval_debug_prem,
  ``Interp.match_rule, ``Interp.invoke_extern_rel,
  ``Interp.invoke_defined_rel, ``Interp.invoke_func_body,
  ``Interp.invoke_extern_func, ``Interp.invoke_builtin_func, ``Interp.match_tablerow,
  ``Interp.invoke_table_func, ``Interp.match_clause, ``Interp.invoke_defined_func]

/-- The invocations the driver pairs with generated calls; their equations
unfold only the invocation the theorem is about. -/
def invocations : List Name := [``Interp.invoke_rel, ``Interp.invoke_func]

/-- The non-recursive definitions of the interpreter and its runtime that
symbolic execution unfolds. -/
def helperFunctions : List Name := [
  ``Interp.assign_var_exp, ``Interp.eval_bool_exp, ``Interp.eval_num_exp, ``Interp.eval_text_exp,
  ``Interp.eval_var_exp, ``Interp.eval_un_bool, ``Interp.eval_un_num, ``Interp.eval_bin_bool,
  ``Interp.eval_bin_num, ``Interp.eval_cmp_bool, ``Interp.eval_cmp_num, ``Interp.numBinop,
  ``Interp.numCmpop, ``Interp.pattern_matches, ``Interp.dot, ``Interp.index_of, ``Interp.index,
  ``Interp.slice, ``Interp.eval_arg_def, ``Interp.subst_targs, ``Interp.typ_note,
  ``Interp.typ_of_value, ``Interp.is_iter_var_exp,
  ``Backtrack.back_err, ``Backtrack.back_unmatch_silent, ``Backtrack.back_unmatch,
  ``Backtrack.back_nest, ``Backtrack.check_back_err, ``Backtrack.choose_sequential,
  ``P4SpecTec.Interp_al.Effects.chooseSequential,
  ``P4SpecTec.Interp_al.Effects.builtin, ``P4SpecTec.Interp_al.Effects.builtinEval,
  ``Ctx.find_rel, ``Ctx.find_rel_opt, ``Ctx.find_func, ``Ctx.find_func_opt, ``Ctx.find_value,
  ``Ctx.find_value_opt, ``Ctx.find_values, ``Ctx.add_value, ``Ctx.localize, ``Ctx.empty,
  ``Ctx.empty_local, ``Ctx.back_undef, ``Ctx.sub_opt, ``Ctx.sub_list, ``Ctx.transpose,
  ``P4SpecTec.Lang.Hints.Input.split, ``P4SpecTec.Domain.Mixfix.args,
  ``P4SpecTec.Domain.Mixfix.to_mixop, ``P4SpecTec.Domain.Mixfix.map,
  ``P4SpecTec.Domain.Mixfix.fill, ``P4SpecTec.Domain.Mixfix.fill.go,
  ``P4SpecTec.Domain.Mixfix.fill.goSeq,
  ``P4SpecTec.Domain.Mixfix.eq_mixop, ``P4SpecTec.Domain.Mixfix.eq,
  ``P4SpecTec.Domain.Mixfix.eq.eqs, ``P4SpecTec.Domain.Mixfix.arity,
  ``P4SpecTec.Runtime.Value.Make.mk, ``P4SpecTec.Runtime.Value.Make.bool,
  ``P4SpecTec.Runtime.Value.Make.nat, ``P4SpecTec.Runtime.Value.Make.int,
  ``P4SpecTec.Runtime.Value.Make.num, ``P4SpecTec.Runtime.Value.Make.text,
  ``P4SpecTec.Runtime.Value.Make.case, ``P4SpecTec.Runtime.Value.Make.tuple,
  ``P4SpecTec.Runtime.Value.Make.opt, ``P4SpecTec.Runtime.Value.Make.list,
  ``P4SpecTec.Runtime.Value.Make.str, ``P4SpecTec.Runtime.Value.Make.func,
  ``P4SpecTec.Runtime.Value.Make.extern,
  ``P4SpecTec.Runtime.Value.Get.bool, ``P4SpecTec.Runtime.Value.Get.num,
  ``P4SpecTec.Runtime.Value.Get.text, ``P4SpecTec.Runtime.Value.Get.str,
  ``P4SpecTec.Runtime.Value.Get.case, ``P4SpecTec.Runtime.Value.Get.tuple,
  ``P4SpecTec.Runtime.Value.Get.opt, ``P4SpecTec.Runtime.Value.Get.list,
  ``P4SpecTec.Prelude.Eval.err?, ``P4SpecTec.Prelude.Eval.unmatch?,
  ``P4SpecTec.Prelude.Eval.ofOption, ``P4SpecTec.Prelude.Eval.check,
  ``P4SpecTec.Prelude.Value.atom, ``P4SpecTec.Prelude.Value.varT,
  ``P4SpecTec.Prelude.valueEq, ``P4SpecTec.Prelude.Iter.idx, ``P4SpecTec.Prelude.Iter.idxInt,
  ``P4SpecTec.Prelude.Num.natSub, ``P4SpecTec.Lang.Xl.Num.bin, ``P4SpecTec.Lang.Xl.Num.cmp,
  ``P4SpecTec.Lang.Xl.Num.un, ``P4SpecTec.Lang.Xl.Num.to_int,
  ``P4SpecTec.Util.Source.mkPhrase]

/-- The lemmas of the calculus and the library that normalise both sides. -/
def calcLemmas : List Name := [
  ``P4SpecTec.Interp_al.Effects.liftPure, ``P4SpecTec.Interp_al.Effects.orElsePure,
  ``P4SpecTec.Interp_al.Effects.notHoldPure,
  ``Q.p_it, ``Q.i_it, ``Q.a_it, ``Q.t_it, ``Q.e_it, ``Q.e_note, ``Q.pa_it, ``Q.pa_note, ``Q.pr_it,
  ``Q.ar_it, ``Q.pm_it, ``Q.nt_it, ``Q.dt_it, ``Q.cl_it, ``Q.rg_it, ``Q.eg_it, ``Q.tr_it, ``Q.d_it,
  ``Q.rp_eq, ``Q.v_eq, ``traced_eq, ``check_rel_inputs_off, ``check_rel_outputs_off,
  ``check_func_inputs_off, ``check_func_output_off, ``Var.eq_eq, ``Atom.eq_eq, ``hOrElse_eq,
  ``orElse_unmatch,
  ``diverge_bind, ``throw_bind, ``mk_run, ``err_some, ``err_none, ``check_true, ``check_false,
  ``canon_mk, ``canon_make_mk, ``canons_append, ``canons_length, ``eq_nat, ``eq_int,
  ``eq_bool, ``eq_text, ``eq_refl,
  ``Outs,
  ``pure_bind, ``bind_assoc, ``bind_pure, ``ite_self, ``List.length_cons, ``List.length_nil,
  ``List.zip_cons_cons, ``List.zip_nil_right, ``List.zip_nil_left, ``List.foldlM_cons,
  ``List.foldlM_nil, ``List.mapM_cons, ``List.mapM_nil, ``List.cons_append, ``List.nil_append,
  ``List.append_nil, ``List.zipIdx, ``List.filterMap_cons, ``List.filterMap_nil,
  ``List.contains, ``List.elem_cons, ``List.elem_nil, ``List.find?_cons, ``List.find?_nil,
  ``List.lookup, ``List.isEmpty, ``List.reverse_cons, ``List.reverse_nil, ``List.range_zero,
  ``List.range_succ, ``List.getElem?_cons_zero, ``List.getElem?_cons_succ, ``List.getElem?_nil,
  ``List.flatMap_cons, ``List.flatMap_nil, ``List.map_cons, ``List.map_nil, ``List.map_append,
  ``List.all_cons,
  ``List.all_nil, ``List.any_cons, ``List.any_nil, ``List.foldl_cons, ``List.foldl_nil,
  ``Option.map_some, ``Option.map_none, ``Option.bind_some, ``Option.bind_none,
  ``Option.bind_eq_bind, ``Option.pure_def, ``Option.map_eq_map, ``bne,
  ``beq_self_eq_true, ``eq_self_iff_true, ``decide_true, ``decide_false, ``Bool.not_true,
  ``Bool.not_false, ``Bool.true_and, ``Bool.false_and, ``Bool.and_true, ``Bool.and_false,
  ``Bool.true_or, ``Bool.false_or, ``Bool.or_true, ``Bool.or_false, ``Bool.not_eq_true',
  ``Bool.not_eq_false', ``and_self, ``and_true, ``true_and, ``and_false, ``false_and,
  ``Int.ofNat_eq_natCast, ``Prod.mk.injEq,
  ``P4SpecTec.Util.Source.info.mk.injEq, ``P4SpecTec.Lang.Il.value'.BoolV.injEq,
  ``P4SpecTec.Lang.Il.value'.NumV.injEq,
  ``P4SpecTec.Lang.Il.value'.TextV.injEq, ``P4SpecTec.Lang.Xl.Num.t.Nat.injEq,
  ``P4SpecTec.Lang.Xl.Num.t.Int.injEq, ``Option.some.injEq, ``List.cons.injEq,
  ``P4SpecTec.Domain.Atom.t.Keyword.injEq, ``P4SpecTec.Domain.Atom.t.Tag.injEq,
  ``P4SpecTec.Domain.Atom.t.Operator.injEq,
  ``ne_eq, ``not_false_eq_true, ``not_true_eq_false, ``Nat.succ_eq_add_one, ``gt_iff_lt,
  ``ge_iff_le, ``Nat.zero_lt_succ, ``Nat.lt_add_one, ``Nat.lt_irrefl, ``Nat.not_lt_zero,
  ``Nat.le_refl, ``Nat.zero_le, ``Nat.add_one_ne_zero, ``Nat.lt_succ_self, ``List.isEmpty_cons,
  ``List.isEmpty_nil, ``Bool.not_not, ``decide_eq_true_eq, ``Bool.decide_eq_true,
  ``instBEqOfDecidableEq, ``beq_iff_eq, ``iter_beq, ``List.beq, ``P4SpecTec.Lang.Il.var.id,
  ``P4SpecTec.Lang.Il.var.typ, ``P4SpecTec.Lang.Il.var.iters, ``P4SpecTec.Lang.Il.iterexp.iter,
  ``P4SpecTec.Lang.Il.iterexp.vars, ``P4SpecTec.Lang.Il.iterprem.iter,
  ``P4SpecTec.Lang.Il.iterprem.vars_bound, ``P4SpecTec.Lang.Il.iterprem.vars_bind,
  ``P4SpecTec.Prelude.ToValue.toValue,
  ``P4SpecTec.Prelude.ToValues.toValues, ``BEq.beq]

/-- The simprocs that decide literals. -/
def simprocs : List Name := [
  ``reduceIte, ``reduceDIte, ``reduceCtorEq, ``String.reduceEq, ``Nat.reduceAdd, ``Nat.reduceSub,
  ``Nat.reduceMul, ``Nat.reduceEqDiff, ``Nat.reduceLT, ``Nat.reduceGT, ``Nat.reduceLeDiff,
  ``Nat.reduceBEq, ``Nat.reduceBNe, ``Int.reduceEq, ``Int.reduceNe, ``Int.reduceOfNat,
  ``Int.reduceAdd, ``Int.reduceSub, ``Int.reduceMul, ``Int.reduceLT, ``Int.reduceLE,
  ``Int.reduceGT, ``Int.reduceGE, ``String.reduceAppend, ``String.reduceBEq, ``String.reduceLT,
  ``Nat.reduceDiv, ``Nat.reduceMod, ``Nat.reducePow, ``Char.reduceEq, ``Int.reduceBEq,
  ``Int.reduceBNe, ``Int.reduceNatCast, ``Nat.reduceBneDiff]

/-- The constants of the library and the prelude whose names say they are
`ToValue` or `BEq` instances, or `toValue` functions: what relating an
interpreter value to a generated value must unfold. -/
def valueConstants (lib : Name) : MetaM (List Name) := do
  let env ← getEnv
  let mut out : List Name := []
  for (n, _) in env.constants.map₂.toList ++ env.constants.map₁.toList do
    let s := n.toString
    let inLib := lib.isPrefixOf n
    let inPrelude := (`P4SpecTec.Prelude).isPrefixOf n
    if (inLib || inPrelude) && !n.isInternal then
      if (s.splitOn ".instToValue").length > 1 then out := n :: out
      else if (s.splitOn ".instBEq").length > 1 then out := n :: out
      else if inLib && (s.splitOn ".toValue").length > 1 && !s.endsWith "toValue.eq_def" then
        out := n :: out
  pure out

/-- The library namespace of the generated definition the goal is about,
from the name of the theorem being proved. -/
def libOf : TacticM Name := do
  let some decl := (← Term.getDeclName?) | throwError "refine_al: no declaration name"
  match decl with
  | .str (.str lib _) _ => pure lib
  | .str lib _ => pure lib
  | _ => throwError "refine_al: unexpected theorem name {decl}"

/-- The equation lemmas of a definition. A definition that matches on a
projection of a parameter gets conditional equations (`v.it = C … →
f v = …`), which `simp` cannot instantiate; for those the unfolding
equation is used instead, and the `match` computes once the value is a
literal. -/
def eqnsOf (n : Name) : MetaM (List Name) := do
  match ← getEqnsFor? n with
  | some eqns =>
    let mut conditional := false
    for e in eqns do
      let info ← getConstInfo e
      let hasHyp ← forallTelescopeReducing info.type fun xs _ => do
        xs.anyM fun x => do isProp (← inferType x)
      if hasHyp then conditional := true
    if conditional then pure [n] else pure eqns.toList
  | none => pure [n]

/-- The local hypotheses to rewrite with: equations whose left side is a
projection of a variable or a `canon` of a variable, and the guard. -/
def factHyps : TacticM (List Name) := do
  (← getMainGoal).withContext do
    let mut out := []
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      -- a hypothesis of a case split decides its condition wherever it occurs
      if decl.userName.toString.startsWith "rf_c" then
        out := decl.userName :: out
        continue
      if let some (_, lhs, rhs) := ty.eq? then
        let lhs := lhs.consumeMData
        let isFact :=
          (lhs.isAppOfArity ``P4SpecTec.Refine.canon 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
          (lhs.isAppOfArity ``canons 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
          (lhs.isAppOfArity ``canonMixfix 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
          (lhs.isAppOfArity ``canonMixfixes 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
          (lhs.isAppOfArity ``canonFields 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
          (lhs.isAppOfArity ``P4SpecTec.Util.Source.info.it 4 &&
            (lhs.getArg! 3).consumeMData.isFVar) ||
          (match lhs with | .proj _ _ x => x.consumeMData.isFVar | _ => false) ||
          (lhs.isAppOf ``Interp.Config.guard) ||
          rhs.consumeMData.isConstOf ``Bool.true || rhs.consumeMData.isConstOf ``Bool.false ||
          (lhs.isAppOfArity ``Ctx.t.global 1) ||
          (lhs.isAppOfArity ``Ctx.local.fenv 1) ||
          (lhs.isAppOf ``Std.HashMap.get?)
        if isFact then out := decl.userName :: out
    pure out.reverse

/-- The names of the whole simp set, once per tactic call. -/
structure SimpSet where
  /-- The lemmas and definitions. -/
  lemmas : Array Name
  /-- The simprocs. -/
  procs : Array Name

/-- Build the simp set. -/
def simpSet : TacticM SimpSet := do
  let lib ← libOf
  let mut lemmas : Array Name := #[]
  for f in blockFunctions do lemmas := lemmas ++ (← eqnsOf f).toArray
  for f in helperFunctions do lemmas := lemmas ++ (← eqnsOf f).toArray
  lemmas := lemmas ++ calcLemmas.toArray
  lemmas := lemmas ++ (← valueConstants lib).toArray
  -- the runtime's `canon` family, by equations
  for f in [``canon', ``canonFields, ``canons, ``canonMixfix, ``canonMixfixes] do
    lemmas := lemmas ++ (← eqnsOf f).toArray
  pure { lemmas, procs := simprocs.toArray }

/-- Run `simp only` with the set and the facts at the goal; `false` when
nothing changed. -/
def normalize (s : SimpSet) : TacticM Bool := timed "normalize" do
  if (← getGoals).isEmpty then return false
  let facts ← factHyps
  let names := s.lemmas ++ facts.toArray
  let args ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let procs ← s.procs.mapM fun n => `(Lean.Parser.Tactic.simpLemma| ↓ $(mkIdent n):ident)
  let all : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems (args ++ procs)
  let s ← saveState
  try
    evalTactic (← `(tactic| simp only [$all,*]))
    pure true
  catch e =>
    s.restore
    let msg := e.toMessageData
    unless (← msg.toString).startsWith "simp made no progress" do
      traceStep m!"normalize failed: {msg}"
    pure false

/-- Run the simp set at a hypothesis. -/
def normalizeAt (s : SimpSet) (h : Name) : TacticM Bool := timed "normalizeAt" do
  if (← getGoals).isEmpty then return false
  let facts := (← factHyps).filter (· != h)
  let names := s.lemmas ++ facts.toArray
  let args ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let procs ← s.procs.mapM fun n => `(Lean.Parser.Tactic.simpLemma| ↓ $(mkIdent n):ident)
  let all : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems (args ++ procs)
  let s ← saveState
  try
    evalTactic (← `(tactic| simp only [$all,*] at $(mkIdent h):ident))
    pure true
  catch e =>
    s.restore
    let msg := e.toMessageData
    unless (← msg.toString).startsWith "simp made no progress" do
      traceStep m!"normalize at {h} failed: {msg}"
    pure false

/-- Normalise every fact (a hypothesis the driver rewrites with) at its
own statement: after a case split, `toValue` of a constructor computes
to a literal, which exposure needs. -/
def normalizeFacts (s : SimpSet) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  for h in ← factHyps do
    -- a fact may become `False` and close the goal
    if (← getGoals).isEmpty then return
    let _ ← normalizeAt s h

/-- Introduce every binder of the goal under an accessible name (the
binder's own when free), so that the facts can be named. -/
partial def introNamed : TacticM Unit := do
  let goal ← getMainGoal
  let ty ← goal.withContext do whnfR (← instantiateMVars (← goal.getType))
  match ty.consumeMData with
  | .forallE bn _ _ _ =>
    let n := if bn.isAnonymous || bn.hasMacroScopes then `rf_x else bn
    let n ← if (← goal.withContext do pure ((← getLCtx).findFromUserName? n).isSome)
      then freshName n.toString else pure n
    evalTactic (← `(tactic| intro $(mkIdent n):ident))
    introNamed
  | _ => pure ()

/-! ## Shapes -/

/-- The head of a monadic chain: `m₁` of `m₁ >>= k`, else the term. -/
def chainHead (m : Expr) : Expr :=
  let m := m.consumeMData
  if m.isAppOfArity ``Bind.bind 6 then (m.getArg! 4).consumeMData else m

/-- The continuation of a monadic chain, if it is a bind. -/
def chainTail (m : Expr) : Option Expr :=
  let m := m.consumeMData
  if m.isAppOfArity ``Bind.bind 6 then some (m.getArg! 5) else none

/-- The `Refines P m n` of the goal. -/
def refinesGoal : TacticM (Option (Expr × Expr × Expr)) := do
  let goal ← getMainGoal
  goal.withContext do
    let ty := (← instantiateMVars (← goal.getType)).consumeMData
    if ty.isAppOfArity ``Refines 5 then
      pure (some ((ty.getArg! 2).consumeMData, (ty.getArg! 3).consumeMData,
        (ty.getArg! 4).consumeMData))
    else pure none

/-- Find the first explicit `Nat` parameter of an interpreter call. Its
signature identifies fuel without assuming that it precedes implicit carrier
and effect-instance parameters. All recognized recursive APIs take fuel as
their first explicit natural parameter. -/
def fuelArgument? (e : Expr) : MetaM (Option Expr) := do
  let mut ty ← inferType e.getAppFn
  for arg in e.getAppArgs do
    ty ← whnf ty
    match ty with
    | .forallE _ dom body bi =>
      if bi.isExplicit && (← whnf dom).isConstOf ``Nat then return some arg.consumeMData
      ty := body.instantiate1 arg
    | _ => return none
  return none

/-- The fuel argument of an interpreter call on a variable fuel in head
position: the head itself, the discriminant of a `match` or the condition
of an `if` at the head, the argument of an option lift, or the body of a
`mapM` at the head. Not inside the alternatives of a match or a
continuation: a split there would copy the whole proof into a zero
branch that does not diverge. -/
partial def stuckFuel (head : Expr) : MetaM (Option FVarId) := do
  let e := head.consumeMData
  let here : Option FVarId ← match e.getAppFn.consumeMData with
    | .const c _ =>
      if (blockFunctions.contains c || invocations.contains c) &&
          e.getAppNumArgs ≥ 1 then
        match ← fuelArgument? e with
        | some (.fvar f) => pure (some f)
        | _ => pure none
      else pure none
    | _ => pure none
  if let some f := here then return some f
  if let some app ← matchMatcherApp? e then
    for d in app.discrs do
      if let some f ← stuckFuel d then return some f
    return none
  if e.isAppOfArity ``ite 5 then return ← stuckFuel (e.getArg! 1)
  if e.isAppOfArity ``P4SpecTec.Prelude.Eval.ofOption 3 then return ← stuckFuel (e.getArg! 2)
  if e.isAppOfArity ``P4SpecTec.Prelude.Eval.err? 2 then return ← stuckFuel (e.getArg! 1)
  if e.isAppOf ``List.mapM && e.getAppNumArgs ≥ 2 then
    -- the body of the iteration
    let f := (e.getArg! (e.getAppNumArgs - 2)).consumeMData
    match f with
    | .lam _ _ b _ => return ← stuckFuel b
    | _ => return ← stuckFuel f
  if e.isAppOf ``List.foldlM && e.getAppNumArgs ≥ 3 then
    let f := (e.getArg! (e.getAppNumArgs - 3)).consumeMData
    match f with
    | .lam _ _ b _ =>
      match b with
      | .lam _ _ b' _ => return ← stuckFuel b'
      | _ => return ← stuckFuel b
    | _ => return ← stuckFuel f
  return none

/-- The generated variable on the right side of a fact, to be split: the
right side mentions only generated data (`toValue` of generated values,
maps of it over generated lists), so any variable in it, the last
argument first, is one. -/
partial def generatedVar (e : Expr) : Option FVarId :=
  match e.consumeMData with
  | .fvar f => some f
  | .app .. => (e.consumeMData.getAppArgs).reverse.findSome? generatedVar
  | _ => none

/-- Whether a variable is of a generated type (or a container of one),
and not of a type of the interpreter's runtime. -/
def isGeneratedVar (lib : Name) (v : FVarId) : MetaM Bool := do
  let ty ← whnfR (← v.getType)
  let runtime := (ty.find? fun e => match e with
    | .const c _ => (`P4SpecTec.Lang).isPrefixOf c || (`P4SpecTec.Util).isPrefixOf c ||
        (`P4SpecTec.Runtime).isPrefixOf c || (`P4SpecTec.Interp_al).isPrefixOf c ||
        (`P4SpecTec.Domain).isPrefixOf c
    | _ => false).isSome
  if runtime then return false
  match ty.getAppFn with
  | .const c _ =>
    pure (lib.isPrefixOf c || c == ``Bool || c == ``List || c == ``Option || c == ``Prod ||
      c == ``Nat || c == ``Int || c == ``String)
  | _ => pure false

/-- The interpreter value the head is stuck on: the first variable of a
`match` discriminant or an `if` condition, with the generated variable
its fact relates it to. -/
def stuckOn (head : Expr) : TacticM (Option FVarId) := timed "stuckOn" do
  (← getMainGoal).withContext do
    -- every match and `if` inside the head, outermost first
    let mut candidates : Array Expr := #[]
    let mut todo : List Expr := [head]
    let mut fuel := 10000
    while fuel > 0 do
      fuel := fuel - 1
      match todo with
      | [] => break
      | e :: rest =>
        todo := rest
        let e := e.consumeMData
        -- only matches: an `if` tests values, it does not inspect their shape
        if let some app ← matchMatcherApp? e then
          candidates := candidates ++ app.discrs
        match e with
        | .app f a => todo := f :: a :: todo
        | .lam _ _ b _ | .forallE _ _ b _ => todo := b :: todo
        | .letE _ _ v b _ => todo := v :: b :: todo
        | .proj _ _ x => todo := x :: todo
        | _ => pure ()
    let mut vars : Array FVarId := #[]
    for d in candidates do
      let ((), st) ← ((← instantiateMVars d).collectFVars).run {}
      for f in st.fvarIds do
        unless vars.contains f do vars := vars.push f
    traceStep m!"stuck on {vars.toList.map Expr.fvar}"
    -- the fact about a stuck variable names the generated variable to split
    for v in vars do
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let ty := (← instantiateMVars decl.type).consumeMData
        if let some (_, lhs, rhs) := ty.eq? then
          let lhs := lhs.consumeMData
          if lhs.isApp && (lhs.getArg! (lhs.getAppNumArgs - 1)).consumeMData == .fvar v then
            if let some g := generatedVar rhs then return some g
    -- a variable of a generated type in the discriminant itself
    let lib ← libOf
    for v in vars do
      if ← isGeneratedVar lib v then return some v
    pure none

/-! ## Facts -/

/-- The `HoldsSpec` hypothesis and the spec it names. -/
def specHyp : TacticM (Option (Name × Name)) := do
  (← getMainGoal).withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if ty.isAppOfArity ``HoldsSpec 2 then
        if let .const spec _ := (ty.getArg! 0).consumeMData.getAppFn.consumeMData then
          return some (decl.userName, spec)
    pure none

/-- The quoted definition constant of the spec definition named `id`, if
the library has one: `Lib.id.al` for a relation or type, `Lib.«$id».al`
for a function. -/
def quotedOf (lib : Name) (id : String) : MetaM (Option Name) := do
  let env ← getEnv
  let candidates := [Name.str (Name.str lib id) "al", Name.str (Name.str lib ("$" ++ id)) "al"]
  pure (candidates.find? env.contains)

/-- The string literals looked up in the global tables inside `e`. -/
partial def tableLookups (e : Expr) : List String :=
  let e := e.consumeMData
  let here := if e.isAppOf ``Std.HashMap.get? && e.getAppNumArgs ≥ 2 then
      match (e.getArg! (e.getAppNumArgs - 1)).consumeMData with
      | .lit (.strVal s) => [s]
      | _ => []
    else []
  here ++ (match e with
    | .app f a => tableLookups f ++ tableLookups a
    | .lam _ t b _ | .forallE _ t b _ => tableLookups t ++ tableLookups b
    | .letE _ t v b _ => tableLookups t ++ tableLookups v ++ tableLookups b
    | .mdata _ e => tableLookups e
    | .proj _ _ e => tableLookups e
    | _ => [])

/-- A proof that the constant `q` is a member of the list the constant
`spec` unfolds to: `List.Mem.tail` for every earlier element, then
`List.Mem.head`. -/
def memProof (spec q : Name) : MetaM Expr := do
  let some info := (← getEnv).find? spec | throwError "refine_al: no spec {spec}"
  let some value := info.value? | throwError "refine_al: {spec} has no value"
  let α := mkConst ``P4SpecTec.Lang.Al.def
  let target := mkConst q
  let rec go (l : Expr) (fuel : Nat) : MetaM Expr := do
    match fuel with
    | 0 => throwError "refine_al: {q} is not in {spec}"
    | fuel + 1 =>
      let l := l.consumeMData
      if l.isAppOfArity ``List.cons 3 then
        let a := l.getArg! 1
        let as := l.getArg! 2
        if a.consumeMData.isConstOf q then
          pure (mkAppN (mkConst ``List.Mem.head [Level.zero]) #[α, target, as])
        else
          pure (mkAppN (mkConst ``List.Mem.tail [Level.zero]) #[α, target, a, as, ← go as fuel])
      else throwError "refine_al: {q} is not in {spec}"
  go value 100000

/-- Derive the table facts for every definition the goal looks up, from
the `HoldsSpec` hypothesis; `true` when a new fact was added. -/
def tableFacts (lib : Name) : TacticM Bool := timed "tableFacts" do
  let some (hspec, spec) ← specHyp | pure false
  let goal ← getMainGoal
  let lookups ← goal.withContext do
    pure (tableLookups (← instantiateMVars (← goal.getType))).eraseDups
  let mut added := false
  for id in lookups do
    let some q ← quotedOf lib id | continue
    let h := Name.mkSimple s!"rf_tbl_{id}"
    if ← (← getMainGoal).withContext do pure ((← getLCtx).findFromUserName? h).isSome then
      continue
    let g ← getMainGoal
    let g' ← g.withContext do
      let hs ← fvarOf hspec
      let mem ← memProof spec q
      let val := mkApp2 (.fvar hs) (mkConst q) mem
      let ty ← inferType val
      let g' ← g.assert h ty val
      let (_, g') ← g'.intro1P
      pure g'
    setGoals [g']
    let _ ← tryTac (evalTactic (← `(tactic| simp only [Holds, $(mkIdent q):ident, Q.d_it, Q.i_it]
      at $(mkIdent h):ident)))
    added := true
  pure added

/-- Expose the shapes the facts determine: every hypothesis
`canon v = ⟨q, n, r⟩` becomes `v.it = ...`, and the lists and mixfixes
inside are destructured, until nothing applies. -/
partial def expose : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let goal ← getMainGoal
  let hyps ← goal.withContext do
    let mut out : Array (Name × Name) := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if let some (_, lhs, rhs) := ty.eq? then
        let lhs := lhs.consumeMData
        let rhs := rhs.consumeMData
        let lemma? : Option Name :=
          if lhs.isAppOfArity ``P4SpecTec.Refine.canon 1 &&
              rhs.isAppOfArity ``P4SpecTec.Util.Source.info.mk 6 then
            some ``canon_eq_it
          else if lhs.isAppOfArity ``canon' 1 then
            match rhs.getAppFn.consumeMData with
            | .const c _ =>
              if c == ``P4SpecTec.Lang.Il.value'.BoolV then some ``canon'_eq_bool
              else if c == ``P4SpecTec.Lang.Il.value'.NumV then some ``canon'_eq_num
              else if c == ``P4SpecTec.Lang.Il.value'.TextV then some ``canon'_eq_text
              else if c == ``P4SpecTec.Lang.Il.value'.StructV then some ``canon'_eq_struct
              else if c == ``P4SpecTec.Lang.Il.value'.CaseV then some ``canon'_eq_case
              else if c == ``P4SpecTec.Lang.Il.value'.TupleV then some ``canon'_eq_tuple
              else if c == ``P4SpecTec.Lang.Il.value'.ListV then some ``canon'_eq_list
              else if c == ``P4SpecTec.Lang.Il.value'.OptV then
                match (rhs.getArg! 0).consumeMData.getAppFn.consumeMData with
                | .const ``Option.none _ => some ``canon'_eq_none
                | .const ``Option.some _ => some ``canon'_eq_some
                | _ => none
              else none
            | _ => none
          else if lhs.isAppOfArity ``canons 1 then
            if rhs.isAppOfArity ``List.nil 1 then some ``canons_eq_nil
            else if rhs.isAppOfArity ``List.cons 3 then some ``canons_eq_cons
            else none
          else if lhs.isAppOfArity ``canonFields 1 then
            if rhs.isAppOfArity ``List.nil 1 then some ``canonFields_eq_nil
            else if rhs.isAppOfArity ``List.cons 3 &&
                (rhs.getArg! 1).consumeMData.isAppOfArity ``Prod.mk 4 then
              some ``canonFields_eq_cons
            else none
          else if lhs.isAppOfArity ``canonMixfix 1 then
            match rhs.getAppFn.consumeMData with
            | .const c _ =>
              if c == ``P4SpecTec.Domain.Mixfix.t.Arg then some ``canonMixfix_eq_arg
              else if c == ``P4SpecTec.Domain.Mixfix.t.Atom then some ``canonMixfix_eq_atom
              else if c == ``P4SpecTec.Domain.Mixfix.t.Brack then some ``canonMixfix_eq_brack
              else if c == ``P4SpecTec.Domain.Mixfix.t.Infix then some ``canonMixfix_eq_infix
              else if c == ``P4SpecTec.Domain.Mixfix.t.Seq then some ``canonMixfix_eq_seq
              else none
            | _ => none
          else if lhs.isAppOfArity ``canonMixfixes 1 then
            if rhs.isAppOfArity ``List.nil 1 then some ``canonMixfixes_eq_nil
            else if rhs.isAppOfArity ``List.cons 3 then some ``canonMixfixes_eq_cons
            else none
          else none
        if let some l := lemma? then out := out.push (decl.userName, l)
    pure out
  if hyps.isEmpty then return
  for (h, l) in hyps do
    -- a contradictory fact closes the goal on the way
    if (← getGoals).isEmpty then return
    let h' ← freshName "rf_h"
    -- the lemma's conclusion is an equation or an existential; destructure fully
    let ok ← timed "expose.have" (tryTac (evalTactic (← `(tactic| have $(mkIdent h'):ident :=
      $(mkIdent l):ident $(mkIdent h):ident))))
    if ok then
      let _ ← timed "expose.clear" (tryTac (evalTactic (← `(tactic| clear $(mkIdent h):ident))))
      destructure h'
  expose
where
  /-- Split existentials and conjunctions, substitute equations on variables. -/
  destructure (h : Name) : TacticM Unit := do
    if (← getGoals).isEmpty then return
    let hid ← fvarOf h
    let ty ← typeOf hid
    let ty := (← (← getMainGoal).withContext (whnfR ty)).consumeMData
    if ty.isAppOfArity ``Exists 2 then
      let x ← freshName "rf_v"
      let h' ← freshName "rf_h"
      timed "expose.obtain" (evalTactic (← `(tactic|
        obtain ⟨$(mkIdent x):ident, $(mkIdent h'):ident⟩ := $(mkIdent h):ident)))
      destructure h'
    else if ty.isAppOfArity ``And 2 then
      let h1 ← freshName "rf_h"
      let h2 ← freshName "rf_g"
      timed "expose.obtain" (evalTactic (← `(tactic|
        obtain ⟨$(mkIdent h1):ident, $(mkIdent h2):ident⟩ := $(mkIdent h):ident)))
      destructure h1
      destructure h2
    else if let some (_, lhs, rhs) := ty.eq? then
      -- `canon v' = w` stays a fact; `vs = v :: vs'` substitutes; `v.it = C ...`
      -- destructures `v`, so that the payload is substituted and every
      -- `match` on it computes
      let lhs := lhs.consumeMData
      let projected : Option FVarId := match lhs with
        | .proj _ _ (.fvar x) => some x
        | _ =>
          if lhs.isAppOfArity ``P4SpecTec.Util.Source.info.it 4 then
            match (lhs.getArg! 3).consumeMData with
            | .fvar x => some x
            | _ => none
          else none
      if lhs.isFVar then
        let _ ← timed "expose.subst" (tryTac (evalTactic (← `(tactic| subst $(mkIdent h):ident))))
      else if rhs.consumeMData.isFVar then
        let _ ← timed "expose.subst" (tryTac (evalTactic (← `(tactic| subst $(mkIdent h):ident))))
      else if let some x := projected then
        let xn ← (← getMainGoal).withContext do pure (← x.getDecl).userName
        let cased ← timed "expose.cases"
          (tryTac (evalTactic (← `(tactic| cases $(mkIdent xn):ident))))
        if cased then
          let _ ← timed "expose.dsimp"
            (tryTac (evalTactic (← `(tactic| dsimp only at $(mkIdent h):ident))))
          let _ ← timed "expose.subst" (tryTac (evalTactic (← `(tactic| subst $(mkIdent h):ident))))

/-! ## The callee step -/

/-- The name of the definition a generated call refers to, and whether it
is a relation: `Lib.R.run` gives `R`, `Lib.«$f»` gives `$f`. -/
def calleeOf (e : Expr) : Option (Name × Bool) :=
  match e.consumeMData.getAppFn.consumeMData with
  | .const (.str (.str lib r) "run") _ => some (.str lib r, true)
  | .const c@(.str _ _) _ => some (c, false)
  | _ => none

/-- The induction hypothesis of the recursion group, if any: a hypothesis
`∀ m, m < fuel → ...`. -/
def groupIH : TacticM (Option Name) := do
  (← getMainGoal).withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      if let .forallE _ d b _ := ty then
        if d.isConstOf ``Nat then
          if let .forallE _ lt _ _ := b then
            if lt.consumeMData.isAppOfArity ``LT.lt 4 then return some decl.userName
    pure none

/-- The conjunct of a group statement that is about the definition `d`:
its index, by the constant named in each conjunct's generated side. -/
def conjunctIndex (stmt : Expr) (d : Name) : MetaM (Option Nat) := do
  let parts := conjuncts stmt
  let rec mentions (e : Expr) : Bool :=
    match e with
    | .const c _ => c == d
    | .app f a => mentions f || mentions a
    | .lam _ t b _ | .forallE _ t b _ => mentions t || mentions b
    | .letE _ t v b _ => mentions t || mentions v || mentions b
    | .mdata _ e => mentions e
    | .proj _ _ e => mentions e
    | _ => false
  pure (parts.findIdx? mentions)

/-- Pair the interpreter's invocation at the head of `m` with the generated
call at the head of `n`: the callee's refinement theorem, or the induction
hypothesis when the callee is in the group. Leaves the value goals and the
continuation. -/
def calleeStep (s : SimpSet) (m n : Expr) : TacticM Unit := timed "callee" do
  let head := chainHead m
  -- a tail call on both sides is the callee's theorem itself; a generated
  -- call without continuation against an interpreter chain is one
  -- followed by `pure`
  let tail := (chainTail m).isNone
  let n ← if (chainTail n).isNone && !tail then do
      evalTactic (← `(tactic| refine refines_of_bind_pure ?_))
      let some (_, _, n') ← refinesGoal | throwError "refine_al: no goal"
      pure n'
    else pure n
  let genHead := chainHead n
  unless genHead.isAppOfArity ``ExceptT.mk 4 do
    throwError "refine_al: the interpreter invokes a definition but the generated code does not:\
      {indentExpr genHead}"
  let call := (genHead.getArg! 3).consumeMData
  let some (callee, _) := calleeOf call | throwError "refine_al: unknown callee {call}"
  let thm := Name.str callee "refines"
  let some fuel ← fuelArgument? head
    | throwError "refine_al: interpreter invocation has no explicit natural fuel parameter"
  -- the callee proof, as a term applied to the fuel and the goal's arguments
  let ih? ← groupIH
  let mut viaIH := false
  let mut proof : Option Term := none
  if let some ih := ih? then
    let ihTy ← (← getMainGoal).withContext do
      instantiateMVars (← (← fvarOf ih).getType)
    -- `∀ m, m < fuel → (A ∧ B ∧ ...)`
    let body := match ihTy with
      | .forallE _ _ (.forallE _ _ b _) _ => b
      | _ => ihTy
    if let some k ← conjunctIndex body call.getAppFn.constName! then
      let n := (conjuncts body).length
      let fuelStx ← Term.exprToSyntax fuel
      let mut t : Term ← `(($(mkIdent ih) $fuelStx (by omega)))
      for _ in List.range k do t ← `(($t).2)
      if k < n - 1 then t ← `(($t).1)
      proof := some t
      viaIH := true
  if proof.isNone then
    unless (← getEnv).contains thm do
      throwError "refine_al: no refinement theorem {thm} for the callee"
    proof := some (mkIdent thm)
  let some p := proof | unreachable!
  traceStep m!"callee {callee} {if viaIH then "by the induction hypothesis" else "by its theorem"}"
  let mut contGoal? : Option MVarId := none
  noteAction "callee: apply"
  if tail then
    evalTactic (← `(tactic| apply $p))
  else
    -- `refines_bind (callee ...) (fun a b h => ...)`
    -- `apply`, not `refine`: the intermediate relation is found by unification
    evalTactic (← `(tactic| apply refines_bind))
    let goals ← (← getGoals).filterM fun g => do pure !(← g.isAssigned)
    let typed ← goals.mapM fun g => do
      pure (g, (← g.withContext do instantiateMVars (← g.getType)).consumeMData)
    let some (calleeGoal, _) := typed.find? fun (_, t) => t.isAppOfArity ``Refines 5
      | throwError "refine_al: no callee goal"
    let some (contGoal, _) := typed.find? fun (_, t) => t.isForall
      | throwError "refine_al: no cont goal"
    contGoal? := some contGoal
    setGoals [calleeGoal]
    evalTactic (← `(tactic| apply $p))
  -- the remaining goals: the guard, the tables, and the value relations
  noteAction "callee: hypotheses"
  let rest ← getGoals
  let mut valueGoals : List MVarId := []
  for g in rest do
    if ← g.isAssigned then continue
    setGoals [g]
    let ty ← g.withContext do instantiateMVars (← g.getType)
    if ty.consumeMData.isAppOfArity ``Rel 4 then
      valueGoals := valueGoals ++ [g]
    else
      unless ← tryTac (evalTactic (← `(tactic| assumption))) do
        let _ ← normalize s
        unless (← getGoals).isEmpty do
          unless ← tryTac (evalTactic (← `(tactic| assumption))) do
            throwError "refine_al: cannot discharge a hypothesis of the callee:\
              {Lean.MessageData.ofGoal g}"
  setGoals (valueGoals ++ contGoal?.toList)

/-! ## The value prover -/

/-- Prove that an interpreter value is related to a generated value, or
that two canonical lists agree, by computing `canon` on both sides with
the facts. -/
def proveValue (s : SimpSet) : TacticM Unit := timed "proveValue" do
  let goal ← getMainGoal
  let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel, Outs])))
  if (← getGoals).isEmpty then return
  let _ ← normalize s
  if (← getGoals).isEmpty then return
  if ← tryTac (evalTactic (← `(tactic| rfl))) then return
  if ← tryTac (evalTactic (← `(tactic| assumption))) then return
  throwError "refine_al: values not related:{Lean.MessageData.ofGoal (← getMainGoal)}\
    \n(from{Lean.MessageData.ofGoal goal})"

/-- The goals that are not the refinement goal (the holes of a `have`),
and the refinement goal. -/
def holesAndMain : TacticM (List MVarId × List MVarId) := do
  let goals ← getGoals
  let typed ← goals.mapM fun g => do
    pure (g, (← g.withContext do instantiateMVars (← g.getType)).consumeMData)
  let (mains, holes) := typed.partition fun (_, t) => t.isAppOfArity ``Refines 5
  pure (holes.map (·.1), mains.map (·.1))

/-! ## Equality tests -/

/-- The `Value.eq` applications inside `e`, in order. -/
partial def valueEqs (e : Expr) : List Expr :=
  let e := e.consumeMData
  let here := if e.isAppOfArity ``P4SpecTec.Runtime.Value.eq 2 then [e] else []
  here ++ (match e with
    | .app f a => valueEqs f ++ valueEqs a
    | .lam _ t b _ | .forallE _ t b _ => valueEqs t ++ valueEqs b
    | .letE _ t v b _ => valueEqs t ++ valueEqs v ++ valueEqs b
    | .mdata _ e => valueEqs e
    | .proj _ _ e => valueEqs e
    | _ => [])

/-- When the interpreter's condition `c` and the generated condition test
values for equality, rewrite the interpreter's tests into the generated
ones (`eq_of_canon`, arguments related by the value prover). Returns the
condition to split on. -/
def alignEqualities (s : SimpSet) (c : Expr) : TacticM Expr := do
  let some (_, m, n) ← refinesGoal | pure c
  let gh := chainHead n
  let c' := if gh.isAppOfArity ``ite 5 then (gh.getArg! 1).consumeMData else c
  let interp := valueEqs (if (chainHead m).isAppOfArity ``ite 5 then (chainHead m).getArg! 1 else c)
  let gen := if c == c' then [] else valueEqs c'
  traceStep m!"align {interp.length} interpreter tests with {gen.length} generated"
  if interp.length != gen.length || interp.isEmpty then
    -- no counterpart: decide the interpreter's tests on their canonical
    -- values, which compute once both are literals
    for a in interp do
      let h ← freshName "rf_eq"
      let a1 ← (← getMainGoal).withContext do Term.exprToSyntax (a.getArg! 0)
      let a2 ← (← getMainGoal).withContext do Term.exprToSyntax (a.getArg! 1)
      let decided ← tryTac (evalTactic (← `(tactic| have $(mkIdent h):ident :
        P4SpecTec.Runtime.Value.eq $a1 $a2 = true :=
          eq_true_of_canon (by simp only [Rel] at *; rfl))))
      let decided ← if decided then pure true else do
        let ok ← tryTac (evalTactic (← `(tactic| have $(mkIdent h):ident :
          P4SpecTec.Runtime.Value.eq $a1 $a2 = true := eq_true_of_canon ?_)))
        if ok then
          let goals ← getGoals
          let (holes, mains) ← holesAndMain
          setGoals holes
          if ← tryTac (proveValue s) then
            setGoals mains
            pure true
          else
            setGoals goals
            pure false
        else pure false
      let decided ← if decided then pure true else do
        let ok ← tryTac (evalTactic (← `(tactic| have $(mkIdent h):ident :
          P4SpecTec.Runtime.Value.eq $a1 $a2 = false := eq_false_of_canon ?_)))
        if ok then
          let goals ← getGoals
          let (holes, mains) ← holesAndMain
          setGoals holes
          let closed ← tryTac (do
            let _ ← tryTac (evalTactic (← `(tactic| intro rf_ne)))
            let _ ← normalizeAt s `rf_ne
            unless (← getGoals).isEmpty do throwError "not decided")
          if closed then
            setGoals mains
            pure true
          else
            setGoals goals
            pure false
        else pure false
      if decided then
        traceStep m!"decided {a}"
        let _ ← tryTac (evalTactic (← `(tactic| simp only [$(mkIdent h):ident])))
    let some (_, m', _) ← refinesGoal | return c
    let h' := chainHead m'
    return (if h'.isAppOfArity ``ite 5 then (h'.getArg! 1).consumeMData else c)
  for (a, b) in interp.zip gen do
    let h ← freshName "rf_eq"
    let a1 ← (← getMainGoal).withContext do Term.exprToSyntax (a.getArg! 0)
    let a2 ← (← getMainGoal).withContext do Term.exprToSyntax (a.getArg! 1)
    let b1 ← (← getMainGoal).withContext do Term.exprToSyntax (b.getArg! 0)
    let b2 ← (← getMainGoal).withContext do Term.exprToSyntax (b.getArg! 1)
    evalTactic (← `(tactic| have $(mkIdent h):ident :
      P4SpecTec.Runtime.Value.eq $a1 $a2 = P4SpecTec.Runtime.Value.eq $b1 $b2 :=
      eq_of_canon ?_ ?_))
    let (holes, mains) ← holesAndMain
    for g in holes do
      setGoals [g]
      proveValue s
    setGoals mains
    let _ ← tryTac (evalTactic (← `(tactic| simp only [$(mkIdent h):ident])))
  let some (_, m', _) ← refinesGoal | pure c
  let h' := chainHead m'
  pure (if h'.isAppOfArity ``ite 5 then (h'.getArg! 1).consumeMData else c')

/-! ## The driver -/

mutual

/-- One step on the main goal; `true` when the goal was closed or split
into goals the loop continues on. -/
partial def step (s : SimpSet) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let _ ← normalize s
  if (← getGoals).isEmpty then return
  normalizeFacts s
  if (← getGoals).isEmpty then return
  expose
  if (← getGoals).isEmpty then return
  if ← tryTac (evalTactic (← `(tactic| contradiction))) then return
  let goal ← getMainGoal
  try stepCore s goal
  catch e =>
    let msg := e.toMessageData
    if ((← msg.toString).splitOn "during ").length > 1 then throw e
    let ty ← goal.withContext do instantiateMVars (← goal.getType)
    let head := if ty.isAppOfArity ``Refines 5 then chainHead (ty.getArg! 3) else ty
    let gen := if ty.isAppOfArity ``Refines 5 then chainHead (ty.getArg! 4) else ty
    goal.withContext do throwError "{msg}\nduring {← phaseNow.get}, at the interpreter step\
      {indentExpr head}\nagainst the generated{indentExpr gen}"

/-- The step proper, on `goal`. -/
partial def stepCore (s : SimpSet) (goal : MVarId) : TacticM Unit := do
  let ty ← goal.withContext do whnfR (← instantiateMVars (← goal.getType))
  -- binders
  if ty.consumeMData.isForall then
    let n ← goal.withContext do
      match ty.consumeMData with
      | .forallE bn _ _ _ => pure bn
      | _ => pure `rf_x
    let n := if n.isAnonymous || n.hasMacroScopes then `rf_x else n
    let n ← if (← goal.withContext do pure ((← getLCtx).findFromUserName? n).isSome)
      then freshName n.toString else pure n
    evalTactic (← `(tactic| intro $(mkIdent n):ident))
    let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel, Outs] at $(mkIdent n):ident)))
    let _ ← tryTac (evalTactic (← `(tactic| dsimp only at $(mkIdent n):ident)))
    let _ ← normalizeAt s n
    expose
    return ← step s
  let some (_, m, n) ← refinesGoal
    | throwError "refine_al: not a refinement goal:{Lean.MessageData.ofGoal goal}"
  -- table entries the interpreter looks up
  if ← tableFacts (← libOf) then
    let _ ← normalize s
    return ← step s
  let head := chainHead m
  -- divergence
  if head.isAppOfArity ``P4SpecTec.Prelude.Eval.diverge 1 then
    traceStep m!"diverge; interpreter side is{indentExpr m}"
    evalTactic (← `(tactic| exact refines_diverge))
    return
  -- a generated `have`
  if n.isAppOfArity ``letFun 4 then
    let f := (n.getArg! 3).consumeMData
    let x := match f with | .lam bn _ _ _ => bn | _ => `rf_x
    let x ← if (← goal.withContext do pure ((← getLCtx).findFromUserName? x).isSome)
      then freshName x.toString else pure x
    let hx ← freshName s!"h{x}"
    noteAction "have"
    traceStep m!"have {x}"
    evalTactic (← `(tactic| refine refines_have fun $(mkIdent x):ident $(mkIdent hx):ident => ?_))
    return ← step s
  -- sequential choice, before any fuel inside the alternatives is split:
  -- a split there would copy the whole proof into a zero branch that
  -- does not diverge
  if m.isAppOfArity ``P4SpecTec.Prelude.Eval.orElse 3 then
    unless n.isAppOfArity ``P4SpecTec.Prelude.Eval.orElse 3 do
      throwError "refine_al: the interpreter chooses but the generated code does not:\
        {Lean.MessageData.ofGoal goal}"
    noteAction "orElse"
    traceStep "orElse"
    evalTactic (← `(tactic| refine refines_orElse ?_ ?_))
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      step s
    return
  -- the fuel
  if let some f ← goal.withContext (stuckFuel head) then
    let fn ← goal.withContext do pure (← f.getDecl).userName
    noteAction "fuel"
    traceStep m!"fuel {fn}"
    let f' ← freshName fn.toString
    -- anonymous holes: a named hole would refer to an earlier goal of that name
    timed "fuel" (evalTactic (← `(tactic| cases $(mkIdent fn):ident with
      | zero => ?_
      | succ $(mkIdent f'):ident => ?_)))
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      let _ ← normalize s
      if (← getGoals).isEmpty then continue
      step s
    return
  -- a pure result
  if head.isAppOfArity ``Pure.pure 4 && (chainTail m).isNone then
    unless n.isAppOfArity ``Pure.pure 4 do
      throwError "refine_al: the interpreter succeeds but the generated code does not:\
        {Lean.MessageData.ofGoal goal}"
    noteAction "pure"
    traceStep "pure"
    evalTactic (← `(tactic| refine refines_pure ?_))
    proveValue s
    return
  -- a failure
  if head.isAppOfArity ``throw 5 && (chainTail m).isNone then
    noteAction "throw"
    traceStep "throw"
    unless ← tryTac (evalTactic (← `(tactic| exact refines_throw))) do
      throwError "refine_al: the interpreter fails but the generated code does not fail alike:\
        {Lean.MessageData.ofGoal goal}"
    return
  -- an invocation
  if invocations.any (head.isAppOf ·) then
    noteAction "callee"
    let tail := (chainTail m).isNone
    calleeStep s m n
    let goals ← getGoals
    let valueGoals := if tail then goals else goals.dropLast
    noteAction "callee: values"
    for g in valueGoals do
      setGoals [g]
      proveValue s
    if tail then
      setGoals []
      return
    setGoals [goals.getLast!]
    return ← step s
  -- the generated side: a match or `if` on a variable, or on a projection
  -- of a variable of a generated structure (destructured first, so that
  -- the projection computes)
  if let some d ← goal.withContext do
      (do
        let gh := chainHead n
        let discrs ← if let some app ← matchMatcherApp? gh then pure app.discrs
          else if gh.isAppOfArity ``ite 5 then pure #[gh.getArg! 1]
          else pure #[]
        -- every match inside the head, outermost first
        let mut inner : Array Expr := #[]
        let mut todo : List Expr := [gh]
        let mut fuel := 10000
        while fuel > 0 do
          fuel := fuel - 1
          match todo with
          | [] => break
          | e :: rest =>
            todo := rest
            let e := e.consumeMData
            if let some app ← matchMatcherApp? e then inner := inner ++ app.discrs
            match e with
            | .app f a => todo := f :: a :: todo
            | .lam _ _ b _ | .forallE _ _ b _ => todo := b :: todo
            | .letE _ _ v b _ => todo := v :: b :: todo
            | .proj _ _ x => todo := x :: todo
            | _ => pure ()
        let lib ← libOf
        let direct ← (discrs ++ inner).filterMapM fun d => do
          match d.consumeMData with
          | .fvar f => if ← isGeneratedVar lib f then pure (some f) else pure none
          | _ => pure none
        if let some f := direct[0]? then
          pure (some f)
        else
          let lib ← libOf
          let mut found : Option FVarId := none
          for d in discrs do
            let ((), st) ← ((← instantiateMVars d).collectFVars).run {}
            for f in st.fvarIds do
              if found.isSome then break
              if ← isGeneratedVar lib f then
                -- a structure of the library: one constructor, no branching
                let ty ← whnfR (← f.getType)
                if let .const c _ := ty.getAppFn then
                  if lib.isPrefixOf c then
                    if let some (.inductInfo info) := (← getEnv).find? c then
                      if info.ctors.length == 1 then found := some f
          pure found) then
    let dn ← goal.withContext do pure (← d.getDecl).userName
    noteAction "cases generated"
    traceStep m!"cases {dn} (generated)"
    timed "cases" (evalTactic (← `(tactic| cases $(mkIdent dn):ident)))
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      noteAction "cases generated: facts"
      normalizeFacts s
      noteAction "cases generated: expose"
      expose
      noteAction "cases generated: normalize"
      let _ ← normalize s
      if (← getGoals).isEmpty then continue
      noteAction "cases generated: step"
      step s
    return
  -- the interpreter side: stuck on a value whose generated counterpart is a variable
  if let some g ← stuckOn head then
    let gn ← goal.withContext do pure (← g.getDecl).userName
    noteAction "cases interpreter"
    traceStep m!"cases {gn} (interpreter)"
    timed "cases" (evalTactic (← `(tactic| cases $(mkIdent gn):ident)))
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      normalizeFacts s
      expose
      let _ ← normalize s
      if (← getGoals).isEmpty then continue
      step s
    return
  -- an `if` on a boolean term on either side
  let cond? : Option Expr :=
    if head.isAppOfArity ``ite 5 then some (head.getArg! 1)
    else
      let gh := chainHead n
      if gh.isAppOfArity ``ite 5 then some (gh.getArg! 1) else none
  if let some c := cond? then
    -- the generated condition, when both sides test: align equality tests
    let c ← alignEqualities s c
    noteAction "split"
    traceStep m!"split on {c}"
    let hc ← freshName "rf_c"
    -- a condition `b = true` splits on the boolean `b`; a proposition by cases
    let b? : Option Expr := match c.consumeMData.eq? with
      | some (_, l, r) =>
        if r.consumeMData.isConstOf ``Bool.true || r.consumeMData.isConstOf ``Bool.false then some l
        else if l.consumeMData.isConstOf ``Bool.true || l.consumeMData.isConstOf ``Bool.false then
          some r
        else none
      | none => none
    let ok ← match b? with
      | some b => do
        let bs ← goal.withContext do Term.exprToSyntax b
        tryTac (evalTactic (← `(tactic| cases $(mkIdent hc):ident : $bs:term)))
      | none => do
        let cs ← goal.withContext do Term.exprToSyntax c
        tryTac (evalTactic (← `(tactic| by_cases $(mkIdent hc):ident : $cs:term)))
    -- a condition that occurs in a dependent position: `split` instead
    unless ok do
      unless ← tryTac (evalTactic (← `(tactic| split))) do
        throwError "refine_al: cannot split on {c}"
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      -- the split's hypothesis decides the condition wherever it occurs
      let _ ← tryTac (evalTactic (← `(tactic| simp only [$(mkIdent hc):ident])))
      if (← getGoals).isEmpty then continue
      let _ ← normalize s
      if (← getGoals).isEmpty then continue
      step s
    return
  -- a generated match on a compound discriminant
  if let some _ ← goal.withContext do matchMatcherApp? (chainHead n) then
    noteAction "split generated match"
    traceStep "split (generated match)"
    if ← tryTac (evalTactic (← `(tactic| split))) then
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        let _ ← tryTac (evalTactic (← `(tactic| subst_vars)))
        normalizeFacts s
        expose
        let _ ← normalize s
        if (← getGoals).isEmpty then continue
        step s
      return
  goal.withContext do
    throwError "refine_al: stuck at the interpreter step{indentExpr head}\nagainst the generated\
      {indentExpr (chainHead n)}\nin{Lean.MessageData.ofGoal goal}"

end

/-- The tactic's body. -/
def refineAl (s : SimpSet) : TacticM Unit := do
  -- the generated definition, unfolded once
  noteAction "entry: intro"
  introNamed
  let goal ← getMainGoal
  goal.withContext do
    let ty := (← instantiateMVars (← goal.getType)).consumeMData
    if ty.isAppOfArity ``Refines 5 then
      let n := (ty.getArg! 4).consumeMData
      if n.isAppOfArity ``ExceptT.mk 4 then
        let call := (n.getArg! 3).consumeMData
        if let .const c _ := call.getAppFn.consumeMData then
          evalTactic (← `(tactic| unfold $(mkIdent c):ident))
  noteAction "entry: Rel"
  let _ ← tryTac (evalTactic (← `(tactic| simp only [Rel] at *)))
  let _ ← normalize s
  -- the invocation the theorem is about: one fuel level, then its body
  noteAction "entry: fuel"
  let some (_, m, _) ← refinesGoal | throwError "refine_al: not a refinement goal"
  let some f ← (← getMainGoal).withContext (stuckFuel m)
    | throwError "refine_al: the interpreter side is not an invocation"
  let fn ← (← getMainGoal).withContext do pure (← f.getDecl).userName
  let f' ← freshName fn.toString
  let mut invEqns : Array Name := #[]
  for i in invocations do invEqns := invEqns ++ (← eqnsOf i).toArray
  let args ← invEqns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let all : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems args
  evalTactic (← `(tactic| cases $(mkIdent fn):ident with
    | zero => (simp only [$all,*]; exact refines_diverge)
    | succ $(mkIdent f'):ident => ?_))
  noteAction "entry: unfold the invocation"
  let _ ← tryTac (evalTactic (← `(tactic| simp only [$all,*])))
  let _ ← normalize s
  expose
  let _ ← normalize s
  phaseTimes.set []
  noteAction "entry: step"
  try step s
  finally traceStep m!"phase times (ms): {← phaseTimes.get}"
  unless (← getGoals).isEmpty do throwError "refine_al: goals left open"

/-- The tactic: see the module docstring. -/
elab "refine_al" : tactic => do
  let s ← simpSet
  -- no error recovery: a failing step must fail the proof, not admit a goal
  try withoutRecover (refineAl s)
  catch e =>
    throwError "{e.toMessageData}\n(last action: {← phaseNow.get})"


end P4SpecTec.Tactic
