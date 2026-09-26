import P4SpecTec.Refine.StateInterp

/-!
Kernel-checked uses of the stateful AL refinement boundary. The fixtures
quantify over fuel and initial state, compose actual function dispatch
through failure/choice/negation, and reject an allocator that resets state.
They are bounded semantic fixtures, not generated full-P4 coverage.
-/

namespace P4SpecTecTest.StateRefinement

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Interp_al
open P4SpecTec.Lang.Il

private def declaration : Lang.Al.def :=
  Q.d (.BuiltinDecD (Q.i "fresh_typeId") [] [] (Q.t .TextT) [])

private def globals : Ctx.global := {
  ftbl := ({} : Std.HashMap String Runtime.Dynamic_al.Func.t).insert
    "fresh_typeId" (.Builtin [] [] (Q.t .TextT)) }
private def cfg : Interp.Config StateEval := { guard := false }
private def call (fuel : Nat) : StateEval value :=
  Interp.do_eval_func fuel cfg globals "fresh_typeId" [] []
private def allocate : StateEval ByteText := do
  pure (ByteText.ofString (← StateEval.freshTypeId))

theorem freshRefines (fuel : Nat) : StateRefines Rel (call fuel) allocate := by
  apply freshStateRefinesOfHolds fuel cfg rfl (Ctx.empty globals) false rfl
  change Holds globals declaration
  simp [Holds, globals, declaration]

/-- info: 'P4SpecTecTest.StateRefinement.freshRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms freshRefines

theorem failureRefines (fuel : Nat) (failure : Fail) :
    StateRefines (fun (_ : value) (_ : ByteText) => False)
      (do let _ ← call fuel; throw failure)
      (do let _ ← allocate; throw failure) := by
  apply stateRefinesBind (freshRefines fuel)
  intro _ _ _
  exact stateRefinesThrow _ failure

/-- info: 'P4SpecTecTest.StateRefinement.failureRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms failureRefines

theorem retryRefines (fuel : Nat) :
    StateRefines Rel
      (StateEval.orElse (do let _ ← call fuel; throw .unmatch) (call fuel))
      (StateEval.orElse (do let _ ← allocate; throw .unmatch) allocate) := by
  apply stateRefinesOrElse ?_ (freshRefines fuel)
  apply stateRefinesBind (freshRefines fuel)
  intro _ _ _
  exact stateRefinesThrow _ .unmatch

/-- info: 'P4SpecTecTest.StateRefinement.retryRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms retryRefines

theorem negativeRefines (fuel : Nat) :
    StateRefines (fun _ _ => True)
      (StateEval.notHold (do let _ ← call fuel; throw (α := value) .unmatch))
      (StateEval.notHold (do let _ ← allocate; throw (α := ByteText) .unmatch)) :=
  stateRefinesNotHold (failureRefines fuel .unmatch)

/-- info: 'P4SpecTecTest.StateRefinement.negativeRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms negativeRefines

-- A kernel-checked counterexample: an allocator that always starts at zero
-- cannot satisfy the exact-state contract, even if its value is ignored.
private def resetAllocate : StateEval ByteText :=
  ExceptT.mk fun _ => StateEval.run allocate 0

theorem resetRejected : ¬ StateRefines (fun (_ : value) (_ : ByteText) => True)
    (call 3) resetAllocate := by
  intro h
  obtain ⟨result, hr, _⟩ := h 5
    (.ok (Runtime.Value.Make.text
      (ByteText.ofString ("FRESH__" ++ toString (5 : FreshState).counter)))) 6 (by
        simp [call, Interp.do_eval_func, Interp.invoke_func, Interp.invoke_func_body,
          Interp.invoke_builtin_func, tracedStateEq, checkFuncInputsStateOff,
          checkFuncOutputStateOff, cfg, Ctx.find_func, Ctx.find_func_opt,
          Ctx.empty, Ctx.empty_local, globals]
        rfl)
  have states := congrArg (Option.map Prod.snd) hr
  change (some (1 : FreshState)) = some 6 at states
  cases states

/-- info: 'P4SpecTecTest.StateRefinement.resetRejected' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resetRejected

end P4SpecTecTest.StateRefinement
