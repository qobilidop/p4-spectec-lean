import P4SpecTec.Refine.Environment
import P4SpecTec.Refine.RealizeFuel
import P4SpecTec.Refine.Quote

/-!
Extern relation invocations under an abstract callback contract. With the guard off and the
relation table holding the declared extern entry, a reference invocation is exactly the
configured callback, after two fuel levels, given the interpreter's own function evaluator
(`do_eval_func` over the same global tables) at the remaining fuel as its trampoline.
Certificates of callers state the contract relating that callback to the generated extern
instance at every trampoline fuel; the concrete target discharges it.
-/

namespace P4SpecTec.Refine

open P4SpecTec.Prelude P4SpecTec.Lang.Il P4SpecTec.Interp_al

/-- With the guard off, an extern relation entry dispatches to the configured callback,
whose trampoline evaluates functions at the remaining fuel. -/
theorem invokeExternRel (fuel : Nat) {cfg : Interp.Config} (hguard : cfg.guard = false)
    (ctx : Ctx.t) (internal : Bool) {name : String} {nottyp : Lang.Il.nottyp}
    {inputs : Lang.Il.Hints.Input.t}
    (hrel : ctx.global.rtbl.get? name = some (.Extern nottyp inputs)) (vs : List value) :
    Interp.invoke_rel (fuel + 2) cfg internal ctx (Q.i name) vs =
      cfg.extern.eval_extern_rel (Interp.do_eval_func fuel cfg ctx.global) name vs := by
  simp only [Interp.invoke_rel, Interp.invoke_extern_rel, traced_eq, Ctx.find_rel,
    Ctx.find_rel_opt, Q.i, Util.Source.mkPhrase, hrel, check_rel_inputs_off hguard,
    check_rel_outputs_off hguard]
  cases internal <;> simp <;> rfl

/-- info: 'P4SpecTec.Refine.invokeExternRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invokeExternRel
#audit_axioms invokeExternRel

/-- A forward extern contract at every trampoline fuel gives the forward refinement of every
reference invocation; the two smallest fuels diverge. -/
theorem externRelRefines {β : Type} {P : List value → β → Prop} {cfg : Interp.Config}
    (hguard : cfg.guard = false) {ctx : Ctx.t} (internal : Bool) {name : String}
    {nottyp : Lang.Il.nottyp} {inputs : Lang.Il.Hints.Input.t}
    (hrel : ctx.global.rtbl.get? name = some (.Extern nottyp inputs)) {vs : List value}
    {n : Eval β}
    (h : ∀ fuel, Refines P (cfg.extern.eval_extern_rel (Interp.do_eval_func fuel cfg ctx.global)
      name vs) n) (fuel : Nat) :
    Refines P (Interp.invoke_rel fuel cfg internal ctx (Q.i name) vs) n := by
  match fuel with
  | 0 => simp only [Interp.invoke_rel]; exact refines_diverge
  | 1 =>
    simp only [Interp.invoke_rel, traced_eq, Ctx.find_rel, Ctx.find_rel_opt, Q.i,
      Util.Source.mkPhrase, hrel, check_rel_inputs_off hguard]
    cases internal <;>
      simp only [Interp.invoke_extern_rel] <;>
      exact refines_diverge
  | fuel + 2 => rw [invokeExternRel fuel hguard ctx internal hrel vs]; exact h fuel

/-- info: 'P4SpecTec.Refine.externRelRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externRelRefines
#audit_axioms externRelRefines

/-- A reverse extern contract gives an eventual reference witness at every fuel above two. -/
theorem externRelRealizes {β : Type} {P : List value → β → Prop} {cfg : Interp.Config}
    (hguard : cfg.guard = false) {ctx : Ctx.t} (internal : Bool) {name : String}
    {nottyp : Lang.Il.nottyp} {inputs : Lang.Il.Hints.Input.t}
    (hrel : ctx.global.rtbl.get? name = some (.Extern nottyp inputs)) {vs : List value}
    {n : Eval β}
    (h : Realizes P (fun fuel => cfg.extern.eval_extern_rel
      (Interp.do_eval_func fuel cfg ctx.global) name vs) n) :
    Realizes P (fun fuel => Interp.invoke_rel fuel cfg internal ctx (Q.i name) vs) n := by
  apply Realizes.ofAdd 2
  simp only [invokeExternRel _ hguard ctx internal hrel vs]
  exact h

/-- info: 'P4SpecTec.Refine.externRelRealizes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externRelRealizes
#audit_axioms externRelRealizes

/-! ## Callback failure collapse

A registered target trampoline turns either failure kind of its callee into a mismatch
(`BackendSim.Make.call_func`). The same collapse applied on both sides preserves both
correspondence directions. -/

/-- The outcome of a computation whose failures are collapsed to a mismatch. -/
def collapseFail {α : Type} : Except Fail α → Except Fail α
  | .ok a => .ok a
  | .error _ => .error .unmatch

/-- Catching every failure as a mismatch collapses the defined outcome. -/
theorem run_catchUnmatch {α : Type} (m : Eval α) :
    (tryCatch m (fun _ => throw .unmatch) : Eval α).run = m.run.map collapseFail := by
  show (ExceptT.tryCatch m _).run = _
  simp only [ExceptT.tryCatch, ExceptT.run_mk]
  change Option.bind m.run _ = _
  cases m.run with
  | none => rfl
  | some r => cases r <;> rfl

/-- info: 'P4SpecTec.Refine.run_catchUnmatch' does not depend on any axioms -/
#guard_msgs in #print axioms run_catchUnmatch

/-- Collapsing failures on both sides preserves forward correspondence. -/
theorem refines_catchUnmatch {α β : Type} {P : α → β → Prop} {m : Eval α} {n : Eval β}
    (h : Refines P m n) :
    Refines P (tryCatch m fun _ => throw .unmatch) (tryCatch n fun _ => throw .unmatch) := by
  intro r hr
  rw [run_catchUnmatch] at hr
  cases hm : m.run with
  | none => rw [hm] at hr; cases hr
  | some s =>
    rw [hm] at hr
    cases hr
    obtain ⟨s', hn, hrel⟩ := h s hm
    refine ⟨collapseFail s', by rw [run_catchUnmatch, hn]; rfl, ?_⟩
    cases s <;> cases s' <;> first | exact hrel | exact absurd hrel id | rfl

/-- info: 'P4SpecTec.Refine.refines_catchUnmatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms refines_catchUnmatch

/-- An eventual witness survives the collapse of its failure kind. -/
theorem EventuallyRuns.catchUnmatch {α : Type} {m : Nat → Eval α} {r : Except Fail α}
    (h : EventuallyRuns m r) :
    EventuallyRuns (fun fuel => tryCatch (m fuel) fun _ => throw .unmatch) (collapseFail r) := by
  obtain ⟨bound, hbound⟩ := h
  exact ⟨bound, fun fuel hfuel => by rw [run_catchUnmatch, hbound fuel hfuel]; rfl⟩

/-- info: 'P4SpecTec.Refine.EventuallyRuns.catchUnmatch' does not depend on any axioms -/
#guard_msgs in #print axioms EventuallyRuns.catchUnmatch

/-- Collapsing failures on both sides preserves reverse correspondence. -/
theorem realizes_catchUnmatch {α β : Type} {P : α → β → Prop} {m : Nat → Eval α}
    {n : Eval β} (h : Realizes P m n) :
    Realizes P (fun fuel => tryCatch (m fuel) fun _ => throw .unmatch)
      (tryCatch n fun _ => throw .unmatch) := by
  intro q hq
  rw [run_catchUnmatch] at hq
  cases hn : n.run with
  | none => rw [hn] at hq; cases hq
  | some s =>
    rw [hn] at hq
    cases hq
    obtain ⟨r, hr, hrel⟩ := h s hn
    refine ⟨collapseFail r, hr.catchUnmatch, ?_⟩
    cases r <;> cases s <;> first | exact hrel | exact absurd hrel id | rfl

/-- info: 'P4SpecTec.Refine.realizes_catchUnmatch' depends on axioms: [propext] -/
#guard_msgs in #print axioms realizes_catchUnmatch

end P4SpecTec.Refine
