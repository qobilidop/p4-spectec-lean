import P4SpecTec.Tactic.Refine.Normalize
import P4SpecTec.Prelude
import P4SpecTec.Refine.Eval
import P4SpecTec.Refine.Syntax

/-!
The forward lockstep driver's interpreter equations, runtime simplifications
and literal simprocs. simpSet selects this preset for the generated library;
normalization itself remains parameterized by SimpSet.
-/

namespace P4SpecTec.Tactic

open Lean Elab Tactic Meta
open P4SpecTec.Refine
open P4SpecTec.Interp_al

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

end P4SpecTec.Tactic
