import P4SpecTec.Refine.Environment
import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Realize
import P4SpecTec.Refine.Value

/-!
Connect operation-specific builtin contracts to actual guard-free AL invocation.
Global lookup and local overrides are explicit; finite fuel entry costs preserve
success, mismatch and hard error alike.
-/

namespace P4SpecTec.Refine.Builtin

open P4SpecTec.Lang.Il P4SpecTec.Prelude P4SpecTec.Interp_al

/-- Lookup, body dispatch and builtin entry consume exactly three fuel steps. -/
theorem invokeRun (fuel : Nat) (cfg : Interp.Config) (hguard : cfg.guard = false)
    (ctx : Ctx.t) (internal : Bool) (cursor : Ctx.cursor) (name : String)
    (tparams : List tparam) (params : List param) (output : typ)
    (targs : List targ) (values : List value)
    (hfind : Ctx.find_func ctx (Q.i name) = pure (cursor, .Builtin tparams params output)) :
    (Interp.invoke_func (fuel + 3) cfg internal ctx (Q.i name) targs values).run =
      (Effects.builtinEval cfg.printHints name targs values).run := by
  simp only [Interp.invoke_func, traced_eq, hfind, check_func_inputs_off hguard]
  cases internal <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
      Effects.liftPure, pure_bind, bind_pure, Interp.invoke_func_body,
      Interp.invoke_builtin_func, check_func_output_off hguard]
  all_goals rfl

/-- info: 'P4SpecTec.Refine.Builtin.invokeRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invokeRun

/-- The actual global declaration and absence of local overrides discharge lookup. -/
theorem invokeRunOfHolds (fuel : Nat) (cfg : Interp.Config) (hguard : cfg.guard = false)
    (ctx : Ctx.t) (internal : Bool) (name : String)
    (tparams : List tparam) (params : List param) (output : typ)
    (targs : List targ) (values : List value) (hfenv : ctx.local.fenv = [])
    (hdecl : Holds ctx.global (Q.d (.BuiltinDecD (Q.i name) tparams params output []))) :
    (Interp.invoke_func (fuel + 3) cfg internal ctx (Q.i name) targs values).run =
      (Effects.builtinEval cfg.printHints name targs values).run := by
  apply invokeRun fuel cfg hguard ctx internal .Global name tparams params output targs values
  change ctx.global.ftbl.get? name = some (.Builtin tparams params output) at hdecl
  simp only [Ctx.find_func, Ctx.find_func_opt, hfenv, List.lookup, hdecl]
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.invokeRunOfHolds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invokeRunOfHolds

/-- A defined builtin outcome occurs in the AL interpreter at every fuel at least three. -/
theorem eventuallyOfHolds (cfg : Interp.Config) (hguard : cfg.guard = false)
    (ctx : Ctx.t) (internal : Bool) (name : String)
    (tparams : List tparam) (params : List param) (output : typ)
    (targs : List targ) (values : List value) (hfenv : ctx.local.fenv = [])
    (hdecl : Holds ctx.global (Q.d (.BuiltinDecD (Q.i name) tparams params output [])))
    {outcome : Except Fail value}
    (run : (Effects.builtinEval cfg.printHints name targs values).run = some outcome) :
    EventuallyRuns (fun fuel => Interp.invoke_func fuel cfg internal ctx
      (Q.i name) targs values) outcome := by
  refine ⟨3, fun fuel enough => ?_⟩
  have fuelEq : fuel = (fuel - 3) + 3 := by omega
  rw [fuelEq, invokeRunOfHolds (fuel - 3) cfg hguard ctx internal name
    tparams params output targs values hfenv hdecl]
  exact run

/-- info: 'P4SpecTec.Refine.Builtin.eventuallyOfHolds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eventuallyOfHolds

/-- Exact canonical observations preserve success correspondence and both failure kinds. -/
theorem resultRelOfCanonical {α : Type} [ToValue α]
    {r : Except Fail value} {q : Except Fail α}
    (h : r.map canon = q.map (fun x => canon (toValue x))) : ResRel Rel r q := by
  cases r <;> cases q <;> simp_all [Except.map, ResRel, Rel]

/-- info: 'P4SpecTec.Refine.Builtin.resultRelOfCanonical' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resultRelOfCanonical

/-- Canonical run equality supplies the forward contract of an operation. -/
theorem refinesOfCanonicalRun {α : Type} [ToValue α]
    {source : Eval value} {generated : Eval α}
    (h : source.run.map (Except.map canon) =
      generated.run.map (Except.map (fun x => canon (toValue x)))) :
    Refines Rel source generated := by
  intro r hr
  rw [hr] at h
  cases hg : generated.run with
  | none => simp [hg] at h
  | some q =>
    refine ⟨q, rfl, resultRelOfCanonical ?_⟩
    exact Option.some.inj (by simpa only [hg, Option.map_some] using h)

/-- info: 'P4SpecTec.Refine.Builtin.refinesOfCanonicalRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms refinesOfCanonicalRun

/-- An operation's exact canonical contract constructs an actual eventual AL execution. -/
theorem realizesOfCanonicalRun {α : Type} [ToValue α]
    (cfg : Interp.Config) (hguard : cfg.guard = false)
    (ctx : Ctx.t) (internal : Bool) (name : String)
    (tparams : List tparam) (params : List param) (output : typ)
    (targs : List targ) (values : List value) (hfenv : ctx.local.fenv = [])
    (hdecl : Holds ctx.global (Q.d (.BuiltinDecD (Q.i name) tparams params output [])))
    {generated : Eval α}
    (h : (Effects.builtinEval cfg.printHints name targs values).run.map (Except.map canon) =
      generated.run.map (Except.map (fun x => canon (toValue x)))) :
    Realizes Rel (fun fuel => Interp.invoke_func fuel cfg internal ctx
      (Q.i name) targs values) generated := by
  intro q hq
  rw [hq] at h
  cases hr : (Effects.builtinEval cfg.printHints name targs values).run with
  | none => simp [hr] at h
  | some r =>
    refine ⟨r, eventuallyOfHolds cfg hguard ctx internal name tparams params output
      targs values hfenv hdecl hr, resultRelOfCanonical ?_⟩
    exact Option.some.inj (by simpa only [hr, Option.map_some] using h)

/-- info: 'P4SpecTec.Refine.Builtin.realizesOfCanonicalRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms realizesOfCanonicalRun

/-- A known builtin cannot finish before lookup, body dispatch and builtin entry. -/
theorem invokeSmallFuel (fuel : Nat) (small : fuel < 3)
    (cfg : Interp.Config) (hguard : cfg.guard = false)
    (ctx : Ctx.t) (internal : Bool) (cursor : Ctx.cursor) (name : String)
    (tparams : List tparam) (params : List param) (output : typ)
    (targs : List targ) (values : List value)
    (hfind : Ctx.find_func ctx (Q.i name) = pure (cursor, .Builtin tparams params output)) :
    (Interp.invoke_func fuel cfg internal ctx (Q.i name) targs values).run = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero =>
      simp only [Interp.invoke_func, traced_eq, hfind, check_func_inputs_off hguard]
      cases internal <;> rfl
    | succ fuel =>
      cases fuel with
      | zero =>
        simp only [Interp.invoke_func, traced_eq, hfind, check_func_inputs_off hguard]
        cases internal <;> rfl
      | succ fuel => omega

/-- info: 'P4SpecTec.Refine.Builtin.invokeSmallFuel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invokeSmallFuel

/-- An exact operation contract covers every finite AL fuel, including entry exhaustion. -/
theorem refinesInvokeOfCanonicalRun {α : Type} [ToValue α]
    (fuel : Nat) (cfg : Interp.Config) (hguard : cfg.guard = false)
    (ctx : Ctx.t) (internal : Bool) (name : String)
    (tparams : List tparam) (params : List param) (output : typ)
    (targs : List targ) (values : List value) (hfenv : ctx.local.fenv = [])
    (hdecl : Holds ctx.global (Q.d (.BuiltinDecD (Q.i name) tparams params output [])))
    {generated : Eval α}
    (h : (Effects.builtinEval cfg.printHints name targs values).run.map (Except.map canon) =
      generated.run.map (Except.map (fun x => canon (toValue x)))) :
    Refines Rel (Interp.invoke_func fuel cfg internal ctx (Q.i name) targs values) generated := by
  intro r hr
  by_cases small : fuel < 3
  · have hfind : Ctx.find_func ctx (Q.i name) = pure (.Global, .Builtin tparams params output) := by
      change ctx.global.ftbl.get? name = some (.Builtin tparams params output) at hdecl
      simp only [Ctx.find_func, Ctx.find_func_opt, hfenv, List.lookup, hdecl]
      rfl
    rw [invokeSmallFuel fuel small cfg hguard ctx internal .Global name
      tparams params output targs values hfind] at hr
    cases hr
  · have fuelEq : fuel = (fuel - 3) + 3 := by omega
    rw [fuelEq, invokeRunOfHolds (fuel - 3) cfg hguard ctx internal name
      tparams params output targs values hfenv hdecl] at hr
    exact refinesOfCanonicalRun h r hr

/-- info: 'P4SpecTec.Refine.Builtin.refinesInvokeOfCanonicalRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms refinesInvokeOfCanonicalRun

end P4SpecTec.Refine.Builtin
