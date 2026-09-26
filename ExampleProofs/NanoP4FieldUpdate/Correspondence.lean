import NanoP4Spec.Refinement.update_fieldValue
import ExampleProofs.NanoP4FieldUpdate.Semantics
import ExampleProofs.NanoP4FieldUpdate.Environment
import ExampleProofs.NanoP4FieldUpdate.Representation

/-!
# Finite-fuel correspondence for field updates

The operational lemmas extract clauses from the actual exported quotation. A structural
raw-list induction constructs a successful interpreter call at fuel `7 * length + 33`.
The existing checked forward refinement theorem then identifies its output, including
for noncanonical notes and source regions. This is a function-level correspondence,
not a proof of the surrounding lvalue evaluation or arbitrary expression effects.
-/

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Interp_al
open Lean Elab Tactic Meta
open P4SpecTec.Lang.Il P4SpecTec.Domain
namespace ExampleProofs.NanoP4FieldUpdate

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

local elab "field_update_raw" : tactic => do
  let mut names := #[]
  for f in P4SpecTec.Tactic.blockFunctions ++ P4SpecTec.Tactic.helperFunctions do
    unless f == ``Interp.assign_exp do
      names := names ++ (← P4SpecTec.Tactic.eqnsOf f).toArray
  names := names ++ P4SpecTec.Tactic.calcLemmas.toArray
  let facts ← P4SpecTec.Tactic.factHyps
  let args ← (names ++ facts.toArray).mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| ↓ $(mkIdent n):ident)
  let procs ← P4SpecTec.Tactic.simprocs.toArray.mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| ↓ $(mkIdent n):ident)
  let all : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems (args ++ procs)
  evalTactic (← `(tactic| simp only [$all,*]))

private def clauses : List Lang.Il.clause :=
  match NanoP4Spec.«$update_fieldValue».al.it with
  | .FuncDecD _ _ _ _ cs _ _ => cs
  | _ => []

private def firstClause : Lang.Il.clause := clauses[0]'(by decide)
private def secondClause : Lang.Il.clause := clauses[1]'(by decide)
private def thirdClause : Lang.Il.clause := clauses[2]'(by decide)

private def clauseEval (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (clause : Lang.Il.clause) (inputs : List Lang.Il.value) : Eval Lang.Il.value := do
  let (localCtx, _, prems, output) ← Interp.match_clause fuel ctx (Ctx.localize ctx) clause inputs
  let localCtx ← Interp.eval_prems fuel cfg localCtx prems
  Interp.eval_exp fuel cfg localCtx output

private def argumentCtx (ctx : Ctx.t) (fields name value : Lang.Il.value) : Ctx.t :=
  Ctx.add_value
    (Ctx.add_value (Ctx.add_value (Ctx.localize ctx) (Q.i "fieldValue", [.List]) fields)
      (Q.i "nameIR", []) name) (Q.i "value", []) value

private theorem assignVar (fuel : Nat) (ctx : Ctx.t) (i : Lang.Il.id) (t : Lang.Il.typ')
    (a : Util.Source.region) (v : Lang.Il.value) :
    Interp.assign_exp (fuel + 1) ctx ⟨.VarE i, t, a⟩ v =
      pure (Ctx.add_value ctx (i, []) v) := by
  cases v with
  | mk it note region => cases it <;> rfl

private theorem assignIter (fuel : Nat) (ctx : Ctx.t) (e : Lang.Il.exp)
    (ie : Lang.Il.iterexp) (t : Lang.Il.typ') (a : Util.Source.region)
    (key : Lang.Il.id × List Lang.Il.iter) (v : Lang.Il.value)
    (h : Interp.is_iter_var_exp ⟨.IterE e ie, t, a⟩ = some key) :
    Interp.assign_exp (fuel + 2) ctx ⟨.IterE e ie, t, a⟩ v =
      pure (Ctx.add_value ctx key v) := by
  cases v with
  | mk it note region =>
    cases it <;> simp only [Interp.assign_exp, Interp.assign_iter_exp, Interp.typ_note, h]

private theorem matchFirst (fuel : Nat) (ctx : Ctx.t) (fields name value : Lang.Il.value) :
    Interp.match_clause (fuel + 7) ctx (Ctx.localize ctx) firstClause [fields, name, value] =
      pure (argumentCtx ctx fields name value, firstClause.it.1,
        firstClause.it.2.2, firstClause.it.2.1) := by
  simp only [firstClause, clauses, NanoP4Spec.«$update_fieldValue».al, Q.d_it,
    List.getElem_cons_zero, Interp.match_clause, Q.cl_it, Interp.assign_args,
    List.length_cons, List.length_nil, beq_self_eq_true, Backtrack.check_back_err,
    ite_true, pure_bind, List.zip_cons_cons, List.zip_nil_left, List.foldlM_cons,
    List.foldlM_nil, Interp.assign_arg, Q.ar_it, Interp.assign_arg_exp]
  simp only [assignVar, assignIter, Q.e, Q.p, Interp.is_iter_var_exp, Q.v_eq,
    Q.i_it, pure_bind, argumentCtx]
  rw [assignIter (fuel + 1) _ _ _ _ _ (Q.i "fieldValue", [.List]) _
    (by simp [Interp.is_iter_var_exp, Lang.Il.var.id, Lang.Il.var.iters])]
  rfl

private theorem invokeEq (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t) (internal : Bool)
    (hg : cfg.guard = false) (hf : ctx.local.fenv = [])
    (hu : Holds ctx.global NanoP4Spec.«$update_fieldValue».al)
    (inputs : List Lang.Il.value) :
    Interp.invoke_func (fuel + 3) cfg internal ctx (Q.i "update_fieldValue") [] inputs =
      Eval.orElse (clauseEval fuel cfg ctx firstClause inputs)
        (Eval.orElse (clauseEval fuel cfg ctx secondClause inputs)
          (clauseEval fuel cfg ctx thirdClause inputs)) := by
  simp only [Holds, NanoP4Spec.«$update_fieldValue».al, Q.d_it, Q.i_it] at hu
  simp only [Interp.invoke_func, traced_eq, check_func_inputs_off hg,
    Ctx.find_func, Ctx.find_func_opt, hf, List.lookup, List.find?_nil, Option.map,
    Q.i_it, hu, Effects.liftPure, pure_bind, ite_self,
    Interp.invoke_func_body, Interp.invoke_defined_func,
    firstClause, secondClause, thirdClause, clauses, NanoP4Spec.«$update_fieldValue».al,
    Q.d_it, clauseEval,
    List.map_cons, List.map_nil, Effects.chooseSequential, Effects.orElsePure,
    Backtrack.choose_sequential, Q.i, Q.p, Backtrack.check_back_err,
    List.length_nil, beq_self_eq_true, List.zip_nil_left, List.foldlM_nil,
    Backtrack.back_unmatch_silent, ite_true, List.getElem_cons_zero,
    List.getElem_cons_succ, orElse_unmatch]

private theorem matchThird (fuel : Nat) (ctx : Ctx.t) (fields name value : Lang.Il.value) :
    Interp.match_clause (fuel + 7) ctx (Ctx.localize ctx) thirdClause [fields, name, value] =
      pure (argumentCtx ctx fields name value, thirdClause.it.1,
        thirdClause.it.2.2, thirdClause.it.2.1) := by
  simp only [thirdClause, clauses, NanoP4Spec.«$update_fieldValue».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Interp.match_clause, Q.cl_it,
    Interp.assign_args, List.length_cons, List.length_nil, beq_self_eq_true,
    Backtrack.check_back_err, ite_true, pure_bind, List.zip_cons_cons, List.zip_nil_left,
    List.foldlM_cons, List.foldlM_nil, Interp.assign_arg, Q.ar_it, Interp.assign_arg_exp]
  simp only [assignVar, assignIter, Q.e, Q.p, Interp.is_iter_var_exp, Q.v_eq,
    Q.i_it, pure_bind, argumentCtx]
  rw [assignIter (fuel + 1) _ _ _ _ _ (Q.i "fieldValue", [.List]) _
    (by simp [Interp.is_iter_var_exp, Lang.Il.var.id, Lang.Il.var.iters])]
  rfl

private theorem nilRaw (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (name value : Lang.Il.value) (ln : Lang.Il.vnote) (la : Util.Source.region) :
    clauseEval (fuel + 15) cfg ctx firstClause
      [⟨.ListV [],ln,la⟩,name,value] =
        pure (Runtime.Value.Make.list (.IterT (Q.t (Q.varT "fieldValue")) .List) []) := by
  unfold clauseEval
  rw [show fuel + 15 = (fuel + 8) + 7 from rfl, matchFirst]
  simp only [pure_bind]
  simp only [firstClause, clauses, NanoP4Spec.«$update_fieldValue».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Q.cl_it]
  unfold argumentCtx
  field_update_raw

private theorem firstCons (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (head name value : Lang.Il.value) (xs : List Lang.Il.value)
    (ln : Lang.Il.vnote) (la : Util.Source.region) :
    clauseEval (fuel + 15) cfg ctx firstClause
      [⟨.ListV (head::xs),ln,la⟩,name,value] =
        some (.error .unmatch) := by
  unfold clauseEval
  rw [show fuel + 15 = (fuel + 8) + 7 from rfl, matchFirst]
  simp only [pure_bind]
  simp only [firstClause, clauses, NanoP4Spec.«$update_fieldValue».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Q.cl_it]
  unfold argumentCtx
  field_update_raw
  rfl


local elab "field_update_step" : tactic => do
  let mut lemmas : Array Name := #[]
  for f in P4SpecTec.Tactic.blockFunctions do
    lemmas := lemmas ++ (← P4SpecTec.Tactic.eqnsOf f).toArray
  for f in P4SpecTec.Tactic.helperFunctions do
    if f != ``P4SpecTec.Domain.Mixfix.fill &&
        f != ``P4SpecTec.Domain.Mixfix.fill.go &&
        f != ``P4SpecTec.Domain.Mixfix.fill.goSeq then
      lemmas := lemmas ++ (← P4SpecTec.Tactic.eqnsOf f).toArray
  lemmas := lemmas ++ P4SpecTec.Tactic.calcLemmas.toArray
  let s : P4SpecTec.Tactic.SimpSet :=
    { lemmas, procs := P4SpecTec.Tactic.simprocs.toArray }
  let facts ← P4SpecTec.Tactic.factHyps
  let args ← (s.lemmas ++ facts.toArray).mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let procs ← s.procs.mapM fun n => `(Lean.Parser.Tactic.simpLemma| ↓ $(mkIdent n):ident)
  let all : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems (args ++ procs)
  let av := mkIdent `ExampleProofs.NanoP4FieldUpdate.assignVar
  let ai := mkIdent `ExampleProofs.NanoP4FieldUpdate.assignIter
  evalTactic (← `(tactic| simp only [$all,*, ↓ $av:ident, ↓ $ai:ident]))


private def matchedCtx (ctx : Ctx.t) (fields name value payload key : Lang.Il.value)
    (tail : List Lang.Il.value) (typ : Lang.Il.typ') : Ctx.t :=
  Ctx.add_value
    (Ctx.add_value
      (Ctx.add_value (argumentCtx ctx fields name value) (Q.i "value_field_h", []) payload)
      (Q.i "nameIR_field_h", []) key)
    (Q.i "fieldValue_t", [.List]) (Runtime.Value.Make.list typ tail)


private theorem thirdNePrem (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (fields payload key name value : Lang.Il.value)
    (tail : List Lang.Il.value) (typ : Lang.Il.typ')
    (heq : Runtime.Value.eq key name = false) :
    Interp.eval_prem (fuel + 14) cfg (matchedCtx ctx fields name value payload key tail typ)
      ((thirdClause.it.2.2)[2]'(by decide)) =
        pure (matchedCtx ctx fields name value payload key tail typ) := by
  simp only [thirdClause, clauses, NanoP4Spec.«$update_fieldValue».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Q.cl_it]
  unfold matchedCtx argumentCtx
  field_update_step

private def thirdParts : Lang.Il.exp × Lang.Il.exp :=
  match thirdClause.it.2.1.it with
  | .ConsE head tail => (head,tail)
  | _ => (thirdClause.it.2.1,thirdClause.it.2.1)

private theorem thirdCall (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (fields payload key name value : Lang.Il.value)
    (tail : List Lang.Il.value) (typ : Lang.Il.typ') :
    Interp.eval_exp (fuel + 28) cfg
      (matchedCtx ctx fields name value payload key tail typ) thirdParts.2 =
      Interp.invoke_func (fuel + 26) cfg true
      (matchedCtx ctx fields name value payload key tail typ)
      (Q.i "update_fieldValue") [] [Runtime.Value.Make.list typ tail, name, value] := by
  simp only [thirdParts, thirdClause, clauses, NanoP4Spec.«$update_fieldValue».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Q.cl_it, Q.e_it]
  simp only [Interp.eval_exp, Interp.eval_call_exp, Interp.subst_targs, pure_bind,
    Interp.eval_args, List.mapM_cons, List.mapM_nil, Interp.eval_arg, Q.ar_it, Q.e_it,
    Interp.eval_var_exp]
  unfold matchedCtx argumentCtx
  field_update_raw

private theorem thirdHead (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (fields payload key name value : Lang.Il.value)
    (tail : List Lang.Il.value) (typ : Lang.Il.typ') :
    Interp.eval_exp (fuel + 14) cfg
      (matchedCtx ctx fields name value payload key tail typ) thirdParts.1 =
      pure (Runtime.Value.Make.case (Q.varT "fieldValue")
        (.Seq [.Arg payload, .Arg key, .Atom (Q.a (.Operator ";"))])) := by
  simp only [thirdParts, thirdClause, clauses, NanoP4Spec.«$update_fieldValue».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Q.cl_it, Q.e_it]
  simp only [Interp.eval_exp, Interp.eval_case_exp, Interp.eval_exps, Q.e_it,
    Interp.typ_note, Q.e_note, Domain.Mixfix.args, Domain.Mixfix.to_mixop,
    Domain.Mixfix.map, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil,
    pure_bind]
  unfold matchedCtx argumentCtx
  field_update_step
  rfl


private theorem thirdOutput (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (fields payload key name value : Lang.Il.value)
    (tail ys : List Lang.Il.value) (typ : Lang.Il.typ') (rn : Lang.Il.vnote)
    (rr : Util.Source.region)
    (hrec : Interp.invoke_func (fuel + 26) cfg true
      (matchedCtx ctx fields name value payload key tail typ)
      (Q.i "update_fieldValue") [] [Runtime.Value.Make.list typ tail, name, value] =
        pure ⟨.ListV ys, rn, rr⟩) :
    ∃ zs, Interp.eval_exp (fuel + 30) cfg
      (matchedCtx ctx fields name value payload key tail typ) thirdClause.it.2.1 =
        pure (Runtime.Value.Make.list (.IterT (Q.t (Q.varT "fieldValue")) .List) zs) := by
  change ∃ zs, (do
    let head ← Interp.eval_exp (fuel + 28) cfg
      (matchedCtx ctx fields name value payload key tail typ) thirdParts.1
    let output ← Interp.eval_exp (fuel + 28) cfg
      (matchedCtx ctx fields name value payload key tail typ) thirdParts.2
    let ys ← Eval.err? (Runtime.Value.Get.list output)
    pure (Runtime.Value.Make.list (.IterT (Q.t (Q.varT "fieldValue")) .List)
      (head :: ys))) = pure (Runtime.Value.Make.list
        (.IterT (Q.t (Q.varT "fieldValue")) .List) zs)
  rw [show fuel + 28 = (fuel + 14) + 14 from rfl, thirdHead]
  simp only [pure_bind]
  rw [thirdCall, hrec]
  exact ⟨_, rfl⟩

private theorem matchSecond (fuel : Nat) (ctx : Ctx.t) (fields name value : Lang.Il.value) :
    Interp.match_clause (fuel + 7) ctx (Ctx.localize ctx) secondClause [fields, name, value] =
      pure (argumentCtx ctx fields name value, secondClause.it.1,
        secondClause.it.2.2, secondClause.it.2.1) := by
  simp only [secondClause, clauses, NanoP4Spec.«$update_fieldValue».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Interp.match_clause, Q.cl_it,
    Interp.assign_args, List.length_cons, List.length_nil, beq_self_eq_true,
    Backtrack.check_back_err, ite_true, pure_bind, List.zip_cons_cons,
    List.zip_nil_left, List.foldlM_cons, List.foldlM_nil, Interp.assign_arg,
    Q.ar_it, Interp.assign_arg_exp]
  simp only [assignVar, assignIter, Q.e, Q.p, Interp.is_iter_var_exp, Q.v_eq,
    Q.i_it, pure_bind, argumentCtx]
  rw [assignIter (fuel + 1) _ _ _ _ _ (Q.i "fieldValue", [.List]) _
    (by simp [Interp.is_iter_var_exp, Lang.Il.var.id, Lang.Il.var.iters])]
  rfl

private theorem secondConsPrem (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (payload key name value : Lang.Il.value) (atom : Lang.Il.atom)
    (tail : List Lang.Il.value) (hn ln : Lang.Il.vnote) (hr lr : Util.Source.region) :
    let fields : Lang.Il.value :=
      ⟨.ListV (⟨.CaseV (.Seq [.Arg payload, .Arg key, .Atom atom]), hn, hr⟩ :: tail), ln, lr⟩
    Interp.eval_prem (fuel + 14) cfg (argumentCtx ctx fields name value)
      ((secondClause.it.2.2)[0]'(by decide)) = pure (argumentCtx ctx fields name value) := by
  dsimp only
  simp only [secondClause, clauses, NanoP4Spec.«$update_fieldValue».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Q.cl_it]
  unfold argumentCtx
  field_update_step

private theorem secondLetPrem (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (payload key name value : Lang.Il.value) (atom : Lang.Il.atom)
    (tail : List Lang.Il.value) (hn ln : Lang.Il.vnote) (hr lr : Util.Source.region) :
    let fields : Lang.Il.value :=
      ⟨.ListV (⟨.CaseV (.Seq [.Arg payload, .Arg key, .Atom atom]), hn, hr⟩ :: tail), ln, lr⟩
    Interp.eval_prem (fuel + 14) cfg (argumentCtx ctx fields name value)
      ((secondClause.it.2.2)[1]'(by decide)) =
        pure (matchedCtx ctx fields name value payload key tail ln.typ) := by
  dsimp only
  simp only [secondClause, clauses, NanoP4Spec.«$update_fieldValue».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Q.cl_it]
  unfold matchedCtx argumentCtx
  field_update_step

private theorem secondEqPrem (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (fields payload key name value : Lang.Il.value)
    (tail : List Lang.Il.value) (typ : Lang.Il.typ')
    (heq : Runtime.Value.eq key name = true) :
    Interp.eval_prem (fuel + 14) cfg (matchedCtx ctx fields name value payload key tail typ)
      ((secondClause.it.2.2)[2]'(by decide)) =
        pure (matchedCtx ctx fields name value payload key tail typ) := by
  simp only [secondClause, clauses, NanoP4Spec.«$update_fieldValue».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Q.cl_it]
  unfold matchedCtx argumentCtx
  field_update_step

private theorem secondOutput (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (fields payload key name value : Lang.Il.value)
    (tail : List Lang.Il.value) (typ : Lang.Il.typ') :
    ∃ output, Interp.eval_exp (fuel + 15) cfg
      (matchedCtx ctx fields name value payload key tail typ) secondClause.it.2.1 =
        some (.ok output) ∧ ∃ ys, output.it = .ListV ys := by
  simp only [secondClause, clauses, NanoP4Spec.«$update_fieldValue».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Q.cl_it, Q.e_it]
  simp only [Interp.eval_exp, Interp.eval_case_exp, Interp.eval_exps, Interp.eval_cons_exp,
    Q.e_it, Interp.typ_note, Q.e_note, Domain.Mixfix.args, Domain.Mixfix.to_mixop,
    Domain.Mixfix.map, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil,
    pure_bind]
  unfold matchedCtx argumentCtx
  field_update_step
  simp only [Domain.Mixfix.fill, Domain.Mixfix.fill.go, Domain.Mixfix.fill.goSeq,
    Option.bind_some, Option.pure_def, pure_bind]
  field_update_step
  refine ⟨_, rfl, _, rfl⟩

private theorem secondRuns (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (payload key name value : Lang.Il.value) (atom : Lang.Il.atom)
    (tail : List Lang.Il.value) (hn ln : Lang.Il.vnote) (hr lr : Util.Source.region)
    (heq : Runtime.Value.eq key name = true) :
    ∃ output, clauseEval (fuel + 15) cfg ctx secondClause
      [⟨.ListV (⟨.CaseV (.Seq [.Arg payload, .Arg key, .Atom atom]), hn, hr⟩ :: tail), ln, lr⟩,
        name, value] = some (.ok output) ∧ ∃ ys, output.it = .ListV ys := by
  unfold clauseEval
  rw [show fuel + 15 = (fuel + 8) + 7 from rfl, matchSecond]
  simp only [pure_bind]
  have shape : secondClause.it.2.2 =
      [(secondClause.it.2.2)[0]'(by decide), (secondClause.it.2.2)[1]'(by decide),
        (secondClause.it.2.2)[2]'(by decide)] := rfl
  rw [Interp.eval_prems, shape]
  simp only [List.foldlM_cons, List.foldlM_nil, secondConsPrem,
    secondLetPrem, secondEqPrem fuel cfg ctx _ payload key name value tail ln.typ heq,
    pure_bind]
  exact secondOutput fuel cfg ctx _ payload key name value tail ln.typ


private theorem secondEqPremFalse (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (fields payload key name value : Lang.Il.value)
    (tail : List Lang.Il.value) (typ : Lang.Il.typ')
    (heq : Runtime.Value.eq key name = false) :
    Interp.eval_prem (fuel + 14) cfg (matchedCtx ctx fields name value payload key tail typ)
      ((secondClause.it.2.2)[2]'(by decide)) = some (.error .unmatch) := by
  simp only [secondClause, clauses, NanoP4Spec.«$update_fieldValue».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Q.cl_it]
  unfold matchedCtx argumentCtx
  field_update_step
  rfl

private theorem secondRejects (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (payload key name value : Lang.Il.value) (atom : Lang.Il.atom)
    (tail : List Lang.Il.value) (hn ln : Lang.Il.vnote) (hr lr : Util.Source.region)
    (heq : Runtime.Value.eq key name = false) :
    clauseEval (fuel + 15) cfg ctx secondClause
      [⟨.ListV (⟨.CaseV (.Seq [.Arg payload, .Arg key, .Atom atom]), hn, hr⟩ :: tail), ln, lr⟩,
        name, value] = some (.error .unmatch) := by
  unfold clauseEval
  rw [show fuel + 15 = (fuel + 8) + 7 from rfl, matchSecond]
  simp only [pure_bind]
  have shape : secondClause.it.2.2 =
      [(secondClause.it.2.2)[0]'(by decide), (secondClause.it.2.2)[1]'(by decide),
        (secondClause.it.2.2)[2]'(by decide)] := rfl
  rw [Interp.eval_prems, shape]
  simp only [List.foldlM_cons, List.foldlM_nil, secondConsPrem,
    secondLetPrem, secondEqPremFalse fuel cfg ctx _ payload key name value tail ln.typ heq,
    pure_bind]
  rfl


private theorem thirdRuns (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (payload key name value : Lang.Il.value) (atom : Lang.Il.atom)
    (tail ys : List Lang.Il.value) (hn ln rn : Lang.Il.vnote)
    (hr lr rr : Util.Source.region) (heq : Runtime.Value.eq key name = false)
    (hrec : Interp.invoke_func (fuel + 26) cfg true
      (matchedCtx ctx
        ⟨.ListV (⟨.CaseV (.Seq [.Arg payload, .Arg key, .Atom atom]), hn, hr⟩ :: tail), ln, lr⟩
        name value payload key tail ln.typ)
      (Q.i "update_fieldValue") [] [Runtime.Value.Make.list ln.typ tail, name, value] =
        pure ⟨.ListV ys, rn, rr⟩) :
    ∃ output, clauseEval (fuel + 30) cfg ctx thirdClause
      [⟨.ListV (⟨.CaseV (.Seq [.Arg payload, .Arg key, .Atom atom]), hn, hr⟩ :: tail), ln, lr⟩,
        name, value] = some (.ok output) ∧ ∃ zs, output.it = .ListV zs := by
  unfold clauseEval
  rw [show fuel + 30 = (fuel + 23) + 7 from rfl, matchThird]
  simp only [pure_bind]
  have shape : thirdClause.it.2.2 =
      [(secondClause.it.2.2)[0]'(by decide), (secondClause.it.2.2)[1]'(by decide),
        (thirdClause.it.2.2)[2]'(by decide)] := rfl
  rw [Interp.eval_prems, shape]
  simp only [List.foldlM_cons, List.foldlM_nil, secondConsPrem,
    secondLetPrem, thirdNePrem (fuel + 15) cfg ctx _ payload key name value tail ln.typ heq,
    pure_bind]
  obtain ⟨zs, hz⟩ := thirdOutput fuel cfg ctx _ payload key name value tail ys ln.typ rn rr hrec
  exact ⟨_, hz, zs, rfl⟩

/-- The raw shape needed by the update helper's argument stripping. -/
private def RawFieldShape (v : Lang.Il.value) : Prop :=
  ∃ x y a, v.it = .CaseV (.Seq [.Arg x, .Arg y, .Atom a])

private theorem rawFieldOfCanon {raw : Lang.Il.value} (f : NanoP4Spec.fieldValue)
    (h : canon raw = canon (toValue f)) : RawFieldShape raw := by
  cases f with
  | semi payload name =>
    have hp := congrArg (·.it) h
    simp only [canon_it, ToValue.toValue, NanoP4Spec.fieldValue.toValue,
      Runtime.Value.Make.case, Runtime.Value.Make.mk, canon', canonMixfix,
      canonMixfixes] at hp
    obtain ⟨m, hm, hc⟩ := canon'_eq_case hp
    obtain ⟨ms, hs, hc⟩ := canonMixfix_eq_seq hc
    obtain ⟨mx, rest, hx, hc, hr⟩ := canonMixfixes_eq_cons hc
    obtain ⟨x, hmx, _⟩ := canonMixfix_eq_arg hc
    obtain ⟨my, rest', hy, hc, hr'⟩ := canonMixfixes_eq_cons hr
    obtain ⟨y, hmy, _⟩ := canonMixfix_eq_arg hc
    obtain ⟨ma, last, ha, hc, hl⟩ := canonMixfixes_eq_cons hr'
    obtain ⟨a, hma, _⟩ := canonMixfix_eq_atom hc
    have hlast := canonMixfixes_eq_nil hl
    refine ⟨x, y, a, ?_⟩
    rw [hm, hs, hx, hmx, hy, hmy, ha, hma, hlast]

/-- Relating to generated fields preserves their raw outer shape. -/
private theorem rawFieldsOfRel {raw : Lang.Il.value} {fs : List NanoP4Spec.fieldValue}
    (h : Refine.Rel raw fs) :
    ∃ xs, raw.it = .ListV xs ∧ ∀ x ∈ xs, RawFieldShape x := by
  have hp := congrArg (·.it) h
  simp only [canon_it, ToValue.toValue, Runtime.Value.Make.list,
    Runtime.Value.Make.mk, canon'] at hp
  obtain ⟨xs, hx, hc⟩ := canon'_eq_list hp
  refine ⟨xs, hx, ?_⟩
  clear h hp hx raw
  induction fs generalizing xs with
  | nil =>
    have he := canons_eq_nil hc
    subst xs
    simp
  | cons f fs ih =>
    change canons xs = canon (toValue f) :: canons (fs.map toValue) at hc
    obtain ⟨x, tail, hx, hh, ht⟩ := canons_eq_cons hc
    subst xs
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact rawFieldOfCanon f hh
    · exact ih tail ht v hv



private theorem rawRealizes (xs : List Lang.Il.value) (hs : ∀ x ∈ xs, RawFieldShape x)
    (cfg : Interp.Config) (ctx : Ctx.t) (internal : Bool)
    (hg : cfg.guard = false) (hf : ctx.local.fenv = [])
    (hu : Holds ctx.global NanoP4Spec.«$update_fieldValue».al)
    (name value : Lang.Il.value) (ln : Lang.Il.vnote) (lr : Util.Source.region) :
    ∃ output, Interp.invoke_func (7 * xs.length + 33) cfg internal ctx
      (Q.i "update_fieldValue") [] [⟨.ListV xs, ln, lr⟩, name, value] =
      some (.ok output) ∧ ∃ ys, output.it = .ListV ys := by
  induction xs generalizing ctx internal ln lr with
  | nil =>
    rw [show 7 * ([] : List Lang.Il.value).length + 33 = 30 + 3 from rfl,
      invokeEq 30 cfg ctx internal hg hf hu, nilRaw 15]
    exact ⟨_, rfl, [], rfl⟩
  | cons head tail ih =>
    obtain ⟨payload, key, atom, hhead⟩ := hs head (by simp)
    have ht : ∀ x ∈ tail, RawFieldShape x := fun x hx => hs x (by simp [hx])
    cases head with
    | mk it hn hr =>
      dsimp only at hhead
      subst it
      rw [show 7 * (⟨.CaseV (.Seq [.Arg payload, .Arg key, .Atom atom]), hn, hr⟩ :: tail).length
          + 33 = (7 * tail.length + 7 + 30) + 3 by simp; omega,
        invokeEq _ cfg ctx internal hg hf hu,
        firstCons (7 * tail.length + 22) cfg ctx _ name value tail ln lr]
      cases heq : Runtime.Value.eq key name with
      | true =>
        obtain ⟨output, ho, ys, hy⟩ := secondRuns (7 * tail.length + 22) cfg ctx
          payload key name value atom tail hn ln hr lr heq
        exact ⟨output, by rw [ho]; rfl, ys, hy⟩
      | false =>
        rw [secondRejects (7 * tail.length + 22) cfg ctx
          payload key name value atom tail hn ln hr lr heq]
        let next := matchedCtx ctx
          ⟨.ListV (⟨.CaseV (.Seq [.Arg payload, .Arg key, .Atom atom]), hn, hr⟩ :: tail),ln,lr⟩
          name value payload key tail ln.typ
        obtain ⟨output, ho, ys, hy⟩ := ih ht next true rfl hu
          (Runtime.Value.Make.note ln.typ) Util.Source.no_region
        cases output with
        | mk it rn rr =>
          dsimp only at hy
          subst it
          have hrec : Interp.invoke_func ((7 * tail.length + 7) + 26) cfg true next
              (Q.i "update_fieldValue") []
              [Runtime.Value.Make.list ln.typ tail, name, value] =
              pure ⟨.ListV ys, rn, rr⟩ := by
            rw [show (7 * tail.length + 7) + 26 = 7 * tail.length + 33 by omega]
            exact ho
          obtain ⟨result, hr, zs, hz⟩ := thirdRuns (7 * tail.length + 7) cfg ctx
            payload key name value atom tail ys hn ln rn hr lr rr heq hrec
          exact ⟨result, by rw [hr]; rfl, zs, hz⟩


private theorem updateMember : NanoP4Spec.«$update_fieldValue».al ∈ NanoP4Spec.spec := by
  run_tac
    let proof ← P4SpecTec.Tactic.memProof `NanoP4Spec.spec `NanoP4Spec.«$update_fieldValue».al
    (← getMainGoal).assign proof
    replaceMainGoal []


private theorem forwardSuccess (fuel : Nat)
    (cfg : Interp.Config) (ctx : Ctx.t) (internal : Bool)
    (hguard : cfg.guard = false) (hfenv : ctx.local.fenv = [])
    (hspec : HoldsSpec NanoP4Spec.spec ctx.global)
    (rawFields rawName rawValue : Lang.Il.value)
    (fields : List NanoP4Spec.fieldValue) (name : NanoP4Spec.nameIR)
    (replacement : NanoP4Spec.value)
    (hfields : Rel rawFields fields) (hname : Rel rawName name)
    (hvalue : Rel rawValue replacement) (output : Lang.Il.value)
    (hrun : Interp.invoke_func fuel cfg internal ctx (Q.i "update_fieldValue") []
      [rawFields, rawName, rawValue] = some (.ok output)) :
    Rel output (update fields name replacement) := by
  have forward := NanoP4Spec.«$update_fieldValue».refines fuel
    cfg ctx internal hguard hfenv hspec rawFields rawName rawValue fields name replacement
    hfields hname hvalue
  obtain ⟨generated, hg, hrel⟩ := forward (.ok output) hrun
  change NanoP4Spec.«$update_fieldValue» fields name replacement = some generated at hg
  rw [generatedEqUpdate] at hg
  cases Option.some.inj hg
  exact hrel


/-- Every related field-list input has a successful finite-fuel execution of the actual
quoted AL function, and its result represents the total generated first-match update.
No termination hypothesis is required; raw notes and source regions are unrestricted. -/
theorem alRealizesUpdate
    (cfg : Interp.Config) (ctx : Ctx.t) (internal : Bool)
    (hguard : cfg.guard = false) (hfenv : ctx.local.fenv = [])
    (hspec : HoldsSpec NanoP4Spec.spec ctx.global)
    (rawFields rawName rawValue : Lang.Il.value)
    (fields : List NanoP4Spec.fieldValue) (name : NanoP4Spec.nameIR)
    (replacement : NanoP4Spec.value)
    (hfields : Rel rawFields fields) (hname : Rel rawName name)
    (hvalue : Rel rawValue replacement) :
    ∃ fuel output,
      Interp.invoke_func fuel cfg internal ctx (Q.i "update_fieldValue") []
        [rawFields, rawName, rawValue] = some (.ok output) ∧
      Rel output (update fields name replacement) := by
  obtain ⟨xs, hx, hs⟩ := rawFieldsOfRel hfields
  cases rawFields with
  | mk it rn rr =>
    dsimp only at hx
    subst it
    have hu : Holds ctx.global NanoP4Spec.«$update_fieldValue».al :=
      hspec NanoP4Spec.«$update_fieldValue».al updateMember
    obtain ⟨output, ho, _⟩ := rawRealizes xs hs cfg ctx internal hguard hfenv
      hu rawName rawValue rn rr
    refine ⟨7 * xs.length + 33, output, ho, ?_⟩
    exact forwardSuccess (7 * xs.length + 33) cfg ctx internal hguard hfenv hspec
      _ rawName rawValue fields name replacement hfields hname hvalue output ho

/-- info: 'ExampleProofs.NanoP4FieldUpdate.alRealizesUpdate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms alRealizesUpdate
#audit_axioms alRealizesUpdate

/-- Actual AL helper execution in the initialized, guard-disabled Nano environment. -/
def referenceUpdate (fuel : Nat) (fields name replacement : Lang.Il.value) :
    Eval Lang.Il.value :=
  Interp_al.Interp.invoke_func fuel { guard := false } false Environment.ctx
    (Refine.Q.i "update_fieldValue") [] [fields, name, replacement]

/-- Sequential reference calls, each with its own finite evaluation budget.
The actual first output is passed directly into the second call. -/
def referenceWrites (firstFuel secondFuel : Nat) (fields : Lang.Il.value)
    (left right : ByteText) (leftValue rightValue : Scalar) : Eval Lang.Il.value := do
  let first ← referenceUpdate firstFuel fields (toValue left) (toValue leftValue.generated)
  referenceUpdate secondFuel first (toValue right) (toValue rightValue.generated)

/-- The observable outcomes of two reference calls, existentially hiding only fuel
and irrelevant source annotations. This does not equate finite-fuel exhaustion with failure. -/
def ReferenceObserves (fields : Lang.Il.value) (left right : ByteText)
    (leftValue rightValue : Scalar) (observation : Lang.Il.value) : Prop :=
  ∃ firstFuel secondFuel output,
    (referenceWrites firstFuel secondFuel fields left right leftValue rightValue).run =
      some (.ok output) ∧ Refine.canon output = observation

/-- Every terminating reference outcome is the corresponding successful field update.
The environment witness and all callee obligations are discharged, not assumptions. -/
theorem referenceSound (fuel : Nat) (fields : List NanoP4Spec.fieldValue)
    (name : ByteText) (replacement : NanoP4Spec.value)
    (rawFields rawName rawReplacement : Lang.Il.value)
    (hfields : Refine.Rel rawFields fields) (hname : Refine.Rel rawName name)
    (hvalue : Refine.Rel rawReplacement replacement)
    (result : Except Fail Lang.Il.value)
    (hresult : (referenceUpdate fuel rawFields rawName rawReplacement).run = some result) :
    ∃ output, result = .ok output ∧ Refine.Rel output (update fields name replacement) := by
  set_option maxRecDepth 8192 in
  have forward := NanoP4Spec.«$update_fieldValue».refines fuel
    { guard := false } Environment.ctx false rfl Environment.localFenvEmpty
    Environment.holdsSpec rawFields rawName rawReplacement fields name replacement
    hfields hname hvalue
  obtain ⟨generated, hg, hrel⟩ := forward result hresult
  change NanoP4Spec.«$update_fieldValue» fields name replacement = some generated at hg
  rw [generatedEqUpdate] at hg
  cases Option.some.inj hg
  cases result with
  | ok output => exact ⟨output, rfl, hrel⟩
  | error e => exact False.elim hrel

/-- info: 'ExampleProofs.NanoP4FieldUpdate.referenceSound' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceSound

/-- Two terminating reference calls produce the two corresponding generated updates. -/
theorem referenceWritesSound (firstFuel secondFuel : Nat) (fields : List Field)
    (rawFields : Lang.Il.value) (hfields : Refine.Rel rawFields (generatedFields fields))
    (left right : ByteText) (leftValue rightValue : Scalar)
    (result : Except Fail Lang.Il.value)
    (hresult : (referenceWrites firstFuel secondFuel rawFields
      left right leftValue rightValue).run = some result) :
    ∃ output, result = .ok output ∧ Refine.Rel output
      (update (update (generatedFields fields) left leftValue.generated)
        right rightValue.generated) := by
  unfold referenceWrites at hresult
  rw [Refine.run_bind] at hresult
  cases hfirst : (referenceUpdate firstFuel rawFields
      (toValue left) (toValue leftValue.generated)).run with
  | none => simp [hfirst] at hresult
  | some first =>
    obtain ⟨middle, hm, hmiddle⟩ := referenceSound firstFuel _ left leftValue.generated
      rawFields (toValue left) (toValue leftValue.generated) hfields rfl rfl first hfirst
    subst first
    simp only [hfirst, Option.bind_some] at hresult
    exact referenceSound secondFuel _ right rightValue.generated middle
      (toValue right) (toValue rightValue.generated) hmiddle rfl rfl result hresult

/-- info: 'ExampleProofs.NanoP4FieldUpdate.referenceWritesSound' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceWritesSound

/-- Every observed reference result agrees with the generated sequential result. -/
theorem referenceObservationSound (fields : List Field) (rawFields : Lang.Il.value)
    (hfields : Refine.Rel rawFields (generatedFields fields))
    (left right : ByteText) (leftValue rightValue : Scalar) (observation : Lang.Il.value)
    (h : ReferenceObserves rawFields left right leftValue rightValue observation) :
    observation = Refine.canon (toValue
      (update (update (generatedFields fields) left leftValue.generated)
        right rightValue.generated)) := by
  obtain ⟨firstFuel, secondFuel, output, hrun, hobs⟩ := h
  obtain ⟨out, hout, hrel⟩ := referenceWritesSound firstFuel secondFuel fields rawFields
    hfields left right leftValue rightValue (.ok output) hrun
  cases Except.ok.inj hout
  exact hobs.symm.trans hrel

/-- info: 'ExampleProofs.NanoP4FieldUpdate.referenceObservationSound' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceObservationSound


/-- Finite-fuel realization with the concrete initialized environment discharged. -/
theorem referenceRealizes (fields : List NanoP4Spec.fieldValue) (name : ByteText)
    (replacement : NanoP4Spec.value) (rawFields rawName rawReplacement : Lang.Il.value)
    (hfields : Rel rawFields fields) (hname : Rel rawName name)
    (hvalue : Rel rawReplacement replacement) :
    ∃ fuel output, (referenceUpdate fuel rawFields rawName rawReplacement).run =
      some (.ok output) ∧ Rel output (update fields name replacement) := by
  exact alRealizesUpdate { guard := false } Environment.ctx false rfl
    Environment.localFenvEmpty Environment.holdsSpec rawFields rawName rawReplacement
    fields name replacement hfields hname hvalue

/-- info: 'ExampleProofs.NanoP4FieldUpdate.referenceRealizes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceRealizes

/-- Both actual reference calls finish at some finite budgets; the first raw output
is reused, without re-encoding, as the input to the second call. -/
theorem referenceWritesRealize (fields : List Field) (rawFields : Lang.Il.value)
    (hfields : Rel rawFields (generatedFields fields))
    (left right : ByteText) (leftValue rightValue : Scalar) :
    ∃ firstFuel secondFuel output,
      (referenceWrites firstFuel secondFuel rawFields left right leftValue rightValue).run =
        some (.ok output) ∧ Rel output
          (update (update (generatedFields fields) left leftValue.generated)
            right rightValue.generated) := by
  obtain ⟨firstFuel, middle, hfirst, hmiddle⟩ := referenceRealizes (generatedFields fields)
    left leftValue.generated rawFields (toValue left) (toValue leftValue.generated)
    hfields rfl rfl
  obtain ⟨secondFuel, output, hsecond, houtput⟩ := referenceRealizes
    (update (generatedFields fields) left leftValue.generated) right rightValue.generated
    middle (toValue right) (toValue rightValue.generated) hmiddle rfl rfl
  refine ⟨firstFuel, secondFuel, output, ?_, houtput⟩
  unfold referenceWrites
  rw [Refine.run_bind, hfirst]
  exact hsecond

/-- info: 'ExampleProofs.NanoP4FieldUpdate.referenceWritesRealize' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceWritesRealize

/-- Exact two-way characterization of the reference consumer's observations.
The reverse implication supplies successful executions, not a termination premise. -/
theorem referenceObservesIff (fields : List Field) (rawFields : Lang.Il.value)
    (hfields : Rel rawFields (generatedFields fields))
    (left right : ByteText) (leftValue rightValue : Scalar) (observation : Lang.Il.value) :
    ReferenceObserves rawFields left right leftValue rightValue observation ↔
      observation = canon (toValue
        (update (update (generatedFields fields) left leftValue.generated)
          right rightValue.generated)) := by
  constructor
  · exact referenceObservationSound fields rawFields hfields left right leftValue rightValue
      observation
  · intro h
    obtain ⟨firstFuel, secondFuel, output, hrun, hrel⟩ :=
      referenceWritesRealize fields rawFields hfields left right leftValue rightValue
    exact ⟨firstFuel, secondFuel, output, hrun, hrel.trans h.symm⟩

/-- info: 'ExampleProofs.NanoP4FieldUpdate.referenceObservesIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceObservesIff

end ExampleProofs.NanoP4FieldUpdate
