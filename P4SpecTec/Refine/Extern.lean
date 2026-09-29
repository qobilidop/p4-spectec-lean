import P4SpecTec.Refine.Environment
import P4SpecTec.Refine.RealizeFuel
import P4SpecTec.Refine.Quote

/-!
Extern relation invocations under an abstract callback contract. With the guard off and the
relation table holding the declared extern entry, a reference invocation is exactly the
configured callback, after two fuel levels. Certificates of callers state the contract
relating that callback to the generated extern instance; the concrete target discharges it.
-/

namespace P4SpecTec.Refine

open P4SpecTec.Prelude P4SpecTec.Lang.Il P4SpecTec.Interp_al

/-- With the guard off, an extern relation entry dispatches to the configured callback. -/
theorem invokeExternRel (fuel : Nat) {cfg : Interp.Config} (hguard : cfg.guard = false)
    (ctx : Ctx.t) (internal : Bool) {name : String} {nottyp : Lang.Il.nottyp}
    {inputs : Lang.Il.Hints.Input.t}
    (hrel : ctx.global.rtbl.get? name = some (.Extern nottyp inputs)) (vs : List value) :
    Interp.invoke_rel (fuel + 2) cfg internal ctx (Q.i name) vs =
      cfg.extern.eval_extern_rel name vs := by
  simp only [Interp.invoke_rel, Interp.invoke_extern_rel, traced_eq, Ctx.find_rel,
    Ctx.find_rel_opt, Q.i, Util.Source.mkPhrase, hrel, check_rel_inputs_off hguard,
    check_rel_outputs_off hguard]
  cases internal <;> simp

/-- info: 'P4SpecTec.Refine.invokeExternRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invokeExternRel
#audit_axioms invokeExternRel

/-- A forward extern contract gives the forward refinement of every reference invocation;
the two smallest fuels diverge. -/
theorem externRelRefines {β : Type} {P : List value → β → Prop} {cfg : Interp.Config}
    (hguard : cfg.guard = false) {ctx : Ctx.t} (internal : Bool) {name : String}
    {nottyp : Lang.Il.nottyp} {inputs : Lang.Il.Hints.Input.t}
    (hrel : ctx.global.rtbl.get? name = some (.Extern nottyp inputs)) {vs : List value}
    {n : Eval β} (h : Refines P (cfg.extern.eval_extern_rel name vs) n) (fuel : Nat) :
    Refines P (Interp.invoke_rel fuel cfg internal ctx (Q.i name) vs) n := by
  match fuel with
  | 0 => simp only [Interp.invoke_rel]; exact refines_diverge
  | 1 =>
    simp only [Interp.invoke_rel, traced_eq, Ctx.find_rel, Ctx.find_rel_opt, Q.i,
      Util.Source.mkPhrase, hrel, check_rel_inputs_off hguard]
    cases internal <;>
      simp only [Interp.invoke_extern_rel] <;>
      exact refines_diverge
  | fuel + 2 => rw [invokeExternRel fuel hguard ctx internal hrel vs]; exact h

/-- info: 'P4SpecTec.Refine.externRelRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externRelRefines
#audit_axioms externRelRefines

/-- A reverse extern contract gives an eventual reference witness at every fuel above two. -/
theorem externRelRealizes {β : Type} {P : List value → β → Prop} {cfg : Interp.Config}
    (hguard : cfg.guard = false) {ctx : Ctx.t} (internal : Bool) {name : String}
    {nottyp : Lang.Il.nottyp} {inputs : Lang.Il.Hints.Input.t}
    (hrel : ctx.global.rtbl.get? name = some (.Extern nottyp inputs)) {vs : List value}
    {n : Eval β} (h : Realizes P (fun _ => cfg.extern.eval_extern_rel name vs) n) :
    Realizes P (fun fuel => Interp.invoke_rel fuel cfg internal ctx (Q.i name) vs) n := by
  apply Realizes.ofAdd 2
  simp only [invokeExternRel _ hguard ctx internal hrel vs]
  exact h

/-- info: 'P4SpecTec.Refine.externRelRealizes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externRelRealizes
#audit_axioms externRelRealizes

end P4SpecTec.Refine
