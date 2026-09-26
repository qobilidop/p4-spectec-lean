import P4SpecTec.Refine.StateCalc

/-!
State-sensitive refinement at the AL interpreter boundary. These lemmas
connect the shared interpreter to the explicit-state calculus, preserving
the exact post-state on every terminating outcome. Guards are explicitly
disabled where the typed generated ABI omits their dynamic checks.
-/

namespace P4SpecTec.Refine

open P4SpecTec.Prelude P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Interp_al
open P4SpecTec.Interp_al.Interp

/-- Exhausted interpreter fuel imposes no obligation on generated execution. -/
theorem stateRefinesDiverge {P : α → β → Prop} (n : StateEval β) :
    StateRefines P (StateEval.liftEval Eval.diverge) n := by
  intro s r t h
  cases h

/-- info: 'P4SpecTec.Refine.stateRefinesDiverge' depends on axioms: [propext] -/
#guard_msgs in #print axioms stateRefinesDiverge

/-- A lifted successful context operation is transparent to state. -/
theorem liftStatePure (a : α) : StateEval.liftEval (pure a) = pure a := rfl

/-- info: 'P4SpecTec.Refine.liftStatePure' does not depend on any axioms -/
#guard_msgs in #print axioms liftStatePure

/-- Tracing observes a stateful computation without changing it. -/
theorem tracedStateEq (cfg : Config StateEval) (label : String) (a : StateEval α) :
    traced cfg label a = a := by
  unfold traced
  split <;> rfl

/-- info: 'P4SpecTec.Refine.tracedStateEq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tracedStateEq

/-- Disabled function input guards are pure successes in the stateful configuration. -/
theorem checkFuncInputsStateOff {cfg : Config StateEval} (h : cfg.guard = false)
    (ctx : Ctx.t) (i : Lang.Il.id) (targs : List targ) (vs : List value) :
    check_func_inputs cfg ctx i targs vs = pure () := by
  unfold check_func_inputs
  simp [h]

/-- info: 'P4SpecTec.Refine.checkFuncInputsStateOff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkFuncInputsStateOff

/-- Disabled function output guards cannot consume or reset state. -/
theorem checkFuncOutputStateOff {cfg : Config StateEval} (h : cfg.guard = false)
    (ctx : Ctx.t) (i : Lang.Il.id) (tparams : List tparam) (t : typ)
    (targs : List targ) (v : value) :
    check_func_output cfg ctx i tparams t targs v = pure () := by
  unfold check_func_output
  simp [h]

/-- info: 'P4SpecTec.Refine.checkFuncOutputStateOff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkFuncOutputStateOff

/-- Fresh builtin dispatch agrees with the typed generated allocator at every state. -/
theorem freshBuiltinStateRefines (hints : P4.Unparse.HEnv) :
    StateRefines Rel (Effects.builtinState hints "fresh_typeId" [] [])
      (do pure (ByteText.ofString (← StateEval.freshTypeId))) := by
  apply stateRefinesBind (stateRefinesRefl StateEval.freshTypeId)
  intro a b h
  cases h
  exact stateRefinesPure rfl

/-- info: 'P4SpecTec.Refine.freshBuiltinStateRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms freshBuiltinStateRefines

/-- The actual AL builtin invocation refines fresh allocation at every interpreter fuel. -/
theorem invokeFreshBuiltinStateRefines (fuel : Nat) (cfg : Config StateEval)
    (hguard : cfg.guard = false) (ctx : Ctx.t) :
    StateRefines Rel
      (invoke_builtin_func fuel cfg ctx (Q.i "fresh_typeId") [] [] [] (Q.t .TextT))
      (do pure (ByteText.ofString (← StateEval.freshTypeId))) := by
  cases fuel with
  | zero => exact stateRefinesDiverge _
  | succ fuel =>
    simp only [invoke_builtin_func, checkFuncOutputStateOff hguard]
    exact freshBuiltinStateRefines cfg.printHints

/-- info: 'P4SpecTec.Refine.invokeFreshBuiltinStateRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms invokeFreshBuiltinStateRefines

/-- Full AL function dispatch refines the typed allocator when lookup selects its declaration.
The statement covers every initial state and every fuel, including exhaustion inside dispatch. -/
theorem invokeFreshStateRefines (fuel : Nat) (cfg : Config StateEval)
    (hguard : cfg.guard = false) (ctx : Ctx.t) (internal : Bool)
    (cursor : Ctx.cursor)
    (hfind : Ctx.find_func ctx (Q.i "fresh_typeId") =
      pure (cursor, .Builtin [] [] (Q.t .TextT))) :
    StateRefines Rel (invoke_func fuel cfg internal ctx (Q.i "fresh_typeId") [] [])
      (do pure (ByteText.ofString (← StateEval.freshTypeId))) := by
  cases fuel with
  | zero => exact stateRefinesDiverge _
  | succ fuel =>
    simp only [invoke_func, tracedStateEq, hfind, checkFuncInputsStateOff hguard]
    cases internal
    all_goals
      cases fuel with
      | zero => exact stateRefinesDiverge _
      | succ fuel => exact invokeFreshBuiltinStateRefines fuel cfg hguard ctx

/-- info: 'P4SpecTec.Refine.invokeFreshStateRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms invokeFreshStateRefines

/-- The usual quoted-definition table contract suffices for fresh function dispatch. -/
theorem freshStateRefinesOfHolds (fuel : Nat) (cfg : Config StateEval)
    (hguard : cfg.guard = false) (ctx : Ctx.t) (internal : Bool)
    (hfenv : ctx.local.fenv = [])
    (hdecl : Holds ctx.global
      (Q.d (.BuiltinDecD (Q.i "fresh_typeId") [] [] (Q.t .TextT) []))) :
    StateRefines Rel (invoke_func fuel cfg internal ctx (Q.i "fresh_typeId") [] [])
      (do pure (ByteText.ofString (← StateEval.freshTypeId))) := by
  apply invokeFreshStateRefines fuel cfg hguard ctx internal .Global
  change ctx.global.ftbl.get? "fresh_typeId" = some (.Builtin [] [] (Q.t .TextT)) at hdecl
  simp only [Ctx.find_func, Ctx.find_func_opt, hfenv, List.lookup, hdecl]
  rfl

/-- info: 'P4SpecTec.Refine.freshStateRefinesOfHolds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms freshStateRefinesOfHolds

/-- Invalid fresh builtin arity is a mismatch before any counter transition. -/
theorem freshBuiltinStateArity (hints : P4.Unparse.HEnv) (targs : List typ)
    (args : List value) (h : targs ≠ [] ∨ args ≠ []) (s : FreshState) :
    StateEval.run (Effects.builtinState hints "fresh_typeId" targs args) s =
      some (.error .unmatch, s) := by
  cases targs <;> cases args <;> simp_all [Effects.builtinState, StateEval.run] <;> rfl

/-- info: 'P4SpecTec.Refine.freshBuiltinStateArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms freshBuiltinStateArity

end P4SpecTec.Refine
