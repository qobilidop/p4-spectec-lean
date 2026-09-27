import NanoP4Spec.Refinement.exists_

/-!
Checked operational bridges for Nano's actual quoted `exists_` helper.
The recursive clause consumes the tail before Boolean disjunction and uses the
actual matched context and raw value notes. `recursiveClause` assumes a finite
successful tail call; it does not certify the recursive generated function.
No generated refinement coverage or general fuel-stability claim is added.
-/

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Interp_al
open Lean Elab Tactic Meta
open P4SpecTec.Lang.Il P4SpecTec.Domain
namespace P4SpecTecTest.NanoReverseExists

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

local elab "exists_raw" : tactic => do
  let mut names := #[]
  for f in P4SpecTec.Tactic.blockFunctions ++ P4SpecTec.Tactic.helperFunctions do
    names := names ++ (← P4SpecTec.Tactic.eqnsOf f).toArray
  names := names ++ (P4SpecTec.Tactic.calcLemmas.filter fun n =>
    n != ``Q.v_eq && n != ``Q.rp_eq).toArray
  let args ← names.mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| ↓ $(mkIdent n):ident)
  let procs ← P4SpecTec.Tactic.simprocs.toArray.mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| ↓ $(mkIdent n):ident)
  let all : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems (args ++ procs)
  evalTactic (← `(tactic| simp only [$all,*]))

def clauses : List Lang.Il.clause :=
  match NanoP4Spec.«$exists_».al.it with
  | .FuncDecD _ _ _ _ cs _ _ => cs
  | _ => []

def firstClause : Lang.Il.clause := clauses[0]'(by decide)
def secondClause : Lang.Il.clause := clauses[1]'(by decide)

def clauseEval (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (clause : Lang.Il.clause) (inputs : List Lang.Il.value) : Eval Lang.Il.value := do
  let (localCtx, _, prems, output) ← Interp.match_clause fuel ctx (Ctx.localize ctx) clause inputs
  let localCtx ← Interp.eval_prems fuel cfg localCtx prems
  Interp.eval_exp fuel cfg localCtx output

def argumentCtx (ctx : Ctx.t) (bits : Lang.Il.value) : Ctx.t :=
  Ctx.add_value (Ctx.localize ctx) (Q.i "b", [.List]) bits

theorem assignVar (fuel : Nat) (ctx : Ctx.t) (i : Lang.Il.id) (t : Lang.Il.typ')
    (a : Util.Source.region) (v : Lang.Il.value) :
    Interp.assign_exp (fuel + 1) ctx ⟨.VarE i, t, a⟩ v =
      pure (Ctx.add_value ctx (i, []) v) := by
  cases v with
  | mk it note region => cases it <;> rfl

/-- info: 'P4SpecTecTest.NanoReverseExists.assignVar' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignVar


theorem assignIter (fuel : Nat) (ctx : Ctx.t) (e : Lang.Il.exp)
    (ie : Lang.Il.iterexp) (t : Lang.Il.typ') (a : Util.Source.region)
    (key : Lang.Il.id × List Lang.Il.iter) (v : Lang.Il.value)
    (h : Interp.is_iter_var_exp ⟨.IterE e ie, t, a⟩ = some key) :
    Interp.assign_exp (fuel + 2) ctx ⟨.IterE e ie, t, a⟩ v =
      pure (Ctx.add_value ctx key v) := by
  cases v with
  | mk it note region =>
    cases it <;> simp only [Interp.assign_exp, Interp.assign_iter_exp, Interp.typ_note, h]

/-- info: 'P4SpecTecTest.NanoReverseExists.assignIter' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignIter


theorem matchFirst (fuel : Nat) (ctx : Ctx.t) (bits : Lang.Il.value) :
    Interp.match_clause (fuel + 7) ctx (Ctx.localize ctx) firstClause [bits] =
      pure (argumentCtx ctx bits, firstClause.it.1,
        firstClause.it.2.2, firstClause.it.2.1) := by
  simp only [firstClause, clauses, NanoP4Spec.«$exists_».al, Q.d_it,
    List.getElem_cons_zero, Interp.match_clause, Q.cl_it, Interp.assign_args,
    List.length_cons, List.length_nil, beq_self_eq_true, Backtrack.check_back_err,
    ite_true, pure_bind, List.zip_cons_cons, List.zip_nil_left, List.foldlM_cons,
    List.foldlM_nil, Interp.assign_arg, Q.ar_it, Interp.assign_arg_exp]
  simp only [assignIter, Q.e, Q.p, Interp.is_iter_var_exp, Q.v_eq,
    Q.i_it, pure_bind, argumentCtx]
  rw [assignIter (fuel + 1) _ _ _ _ _ (Q.i "b", [.List]) _
    (by simp [Interp.is_iter_var_exp, Lang.Il.var.id, Lang.Il.var.iters])]
  rfl

/-- info: 'P4SpecTecTest.NanoReverseExists.matchFirst' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matchFirst


theorem matchSecond (fuel : Nat) (ctx : Ctx.t) (bits : Lang.Il.value) :
    Interp.match_clause (fuel + 7) ctx (Ctx.localize ctx) secondClause [bits] =
      pure (argumentCtx ctx bits, secondClause.it.1,
        secondClause.it.2.2, secondClause.it.2.1) := by
  simp only [secondClause, clauses, NanoP4Spec.«$exists_».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Interp.match_clause, Q.cl_it,
    Interp.assign_args, List.length_cons, List.length_nil, beq_self_eq_true,
    Backtrack.check_back_err, ite_true, pure_bind, List.zip_cons_cons, List.zip_nil_left,
    List.foldlM_cons, List.foldlM_nil, Interp.assign_arg, Q.ar_it, Interp.assign_arg_exp]
  simp only [assignIter, Q.e, Q.p, Interp.is_iter_var_exp, Q.v_eq,
    Q.i_it, pure_bind, argumentCtx]
  rw [assignIter (fuel + 1) _ _ _ _ _ (Q.i "b", [.List]) _
    (by simp [Interp.is_iter_var_exp, Lang.Il.var.id, Lang.Il.var.iters])]
  rfl

/-- info: 'P4SpecTecTest.NanoReverseExists.matchSecond' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matchSecond


theorem invokeEq (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t) (internal : Bool)
    (hg : cfg.guard = false) (hf : ctx.local.fenv = [])
    (hu : Holds ctx.global NanoP4Spec.«$exists_».al)
    (inputs : List Lang.Il.value) :
    Interp.invoke_func (fuel + 3) cfg internal ctx (Q.i "exists_") [] inputs =
      Eval.orElse (clauseEval fuel cfg ctx firstClause inputs)
        (clauseEval fuel cfg ctx secondClause inputs) := by
  simp only [Holds, NanoP4Spec.«$exists_».al, Q.d_it, Q.i_it] at hu
  simp only [Interp.invoke_func, traced_eq, check_func_inputs_off hg,
    Ctx.find_func, Ctx.find_func_opt, hf, List.lookup, List.find?_nil, Option.map,
    Q.i_it, hu, Effects.liftPure, pure_bind, ite_self,
    Interp.invoke_func_body, Interp.invoke_defined_func,
    firstClause, secondClause, clauses, NanoP4Spec.«$exists_».al,
    Q.d_it, clauseEval, List.map_cons, List.map_nil, Effects.chooseSequential,
    Effects.orElsePure, Backtrack.choose_sequential, Q.i, Q.p, Backtrack.check_back_err,
    List.length_nil, beq_self_eq_true, List.zip_nil_left, List.foldlM_nil,
    Backtrack.back_unmatch_silent, ite_true, List.getElem_cons_zero,
    List.getElem_cons_succ, orElse_unmatch]

/-- info: 'P4SpecTecTest.NanoReverseExists.invokeEq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invokeEq


theorem nilRaw (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (ln : Lang.Il.vnote) (la : Util.Source.region) :
    clauseEval (fuel + 15) cfg ctx firstClause [⟨.ListV [],ln,la⟩] =
      pure (Runtime.Value.Make.bool false) := by
  unfold clauseEval
  rw [show fuel + 15 = (fuel + 8) + 7 from rfl, matchFirst]
  simp only [pure_bind]
  simp only [firstClause, clauses, NanoP4Spec.«$exists_».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Q.cl_it]
  unfold argumentCtx
  exists_raw

/-- info: 'P4SpecTecTest.NanoReverseExists.nilRaw' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nilRaw


theorem firstCons (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (head : Lang.Il.value) (xs : List Lang.Il.value)
    (ln : Lang.Il.vnote) (la : Util.Source.region) :
    clauseEval (fuel + 15) cfg ctx firstClause [⟨.ListV (head::xs),ln,la⟩] =
      some (.error .unmatch) := by
  unfold clauseEval
  rw [show fuel + 15 = (fuel + 8) + 7 from rfl, matchFirst]
  simp only [pure_bind]
  simp only [firstClause, clauses, NanoP4Spec.«$exists_».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Q.cl_it]
  unfold argumentCtx
  exists_raw
  rfl

/-- info: 'P4SpecTecTest.NanoReverseExists.firstCons' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firstCons


def matchedCtx (ctx : Ctx.t) (bits head : Lang.Il.value)
    (xs : List Lang.Il.value) (typ : typ') : Ctx.t :=
  Ctx.add_value (Ctx.add_value (argumentCtx ctx bits) (Q.i "b_h", []) head)
    (Q.i "b_t", [.List]) (Runtime.Value.Make.list typ xs)

theorem recursiveClause (fuel : Nat) (cfg : Interp.Config) (ctx : Ctx.t)
    (b : Bool) (xs : List Lang.Il.value)
    (bn ln : Lang.Il.vnote) (ba la : Util.Source.region) (c : Bool)
    (hrec : Interp.invoke_func (fuel + 26) cfg true
      (matchedCtx ctx ⟨.ListV (⟨.BoolV b,bn,ba⟩::xs),ln,la⟩ ⟨.BoolV b,bn,ba⟩ xs ln.typ)
      (Q.i "exists_") [] [Runtime.Value.Make.list ln.typ xs] =
        some (.ok (Runtime.Value.Make.bool c))) :
    clauseEval (fuel + 30) cfg ctx secondClause
      [⟨.ListV (⟨.BoolV b,bn,ba⟩::xs),ln,la⟩] =
      pure (Runtime.Value.Make.bool (b || c)) := by
  unfold clauseEval
  rw [show fuel + 30 = (fuel + 23) + 7 from rfl, matchSecond]
  simp only [pure_bind]
  simp only [secondClause, clauses, NanoP4Spec.«$exists_».al, Q.d_it,
    List.getElem_cons_zero, List.getElem_cons_succ, Q.cl_it]
  unfold argumentCtx
  unfold matchedCtx argumentCtx at hrec
  dsimp only [Ctx.add_value, Ctx.localize, Ctx.empty_local, Q.i, Q.p,
    Runtime.Value.Make.list, Runtime.Value.Make.mk] at hrec
  exists_raw
  rw [hrec]
  rfl

/-- info: 'P4SpecTecTest.NanoReverseExists.recursiveClause' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recursiveClause


theorem rawOfRel {raw : Lang.Il.value} {bs : List Bool} (h : Rel raw bs) :
    ∃ xs, raw.it = .ListV xs ∧ canons xs = canons (bs.map toValue) := by
  have hp := congrArg (·.it) h
  simp only [canon_it, ToValue.toValue, Runtime.Value.Make.list,
    Runtime.Value.Make.mk, canon'] at hp
  exact canon'_eq_list hp

/-- info: 'P4SpecTecTest.NanoReverseExists.rawOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rawOfRel


theorem boolOfRel {raw : Lang.Il.value} {b : Bool} (h : Rel raw b) :
    raw.it = .BoolV b := by
  have hp := congrArg (·.it) h
  simp only [canon_it, ToValue.toValue, Runtime.Value.Make.bool,
    Runtime.Value.Make.mk, canon'] at hp
  exact canon'_eq_bool hp

/-- info: 'P4SpecTecTest.NanoReverseExists.boolOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boolOfRel


theorem member : NanoP4Spec.«$exists_».al ∈ NanoP4Spec.spec := by
  run_tac
    let proof ← P4SpecTec.Tactic.memProof `NanoP4Spec.spec `NanoP4Spec.«$exists_».al
    (← getMainGoal).assign proof
    replaceMainGoal []

/-- info: 'P4SpecTecTest.NanoReverseExists.member' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms member


end P4SpecTecTest.NanoReverseExists
