import Lean.Elab.Command
import P4SpecTec.Codegen.Funcs
import P4SpecTec.Refine.StateInterp

/-!
Refinement against an allocator parsed and elaborated from the actual builtin
emitter. These bounded proofs exercise generated output and exact state;
they do not enable production stateful generation or claim all-definition coverage.
-/

namespace P4SpecTecTest.StateGeneratedRefinement

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Interp_al
open P4SpecTec.Codegen P4SpecTec.Lang.Il

private def declaration : Lang.Al.def :=
  Q.d (.BuiltinDecD (Q.i "fresh_typeId") [] [] (Q.t .TextT) [])

-- No handwritten substitute for the emitted definition appears in the proof target.
open Lean Elab Command in
run_cmd do
  let env := Env.ofSpec "P4SpecTecTest.StateGeneratedRefinement" [declaration]
  unless env.mode == .freshState do throwError "fresh declaration did not select state mode"
  let source ← match Funcs.builtinDecl env "fresh_typeId" [] [] .TextT with
    | .ok text => pure (Codegen.render text)
    | .error err => throwError "fresh allocator emission failed: {err}"
  let stx ← match Lean.Parser.runParserCategory (← getEnv) `command source with
    | .ok stx => pure stx
    | .error err => throwError "fresh allocator did not parse:\n{source}\n{err}"
  elabCommand stx

theorem emittedFreshRefines (fuel : Nat) (cfg : Interp.Config StateEval)
    (hguard : cfg.guard = false) (ctx : Ctx.t) (internal : Bool)
    (hfenv : ctx.local.fenv = [])
    (hdecl : Holds ctx.global declaration) :
    StateRefines Rel
      (Interp.invoke_func fuel cfg internal ctx (Q.i "fresh_typeId") [] [])
      (ExceptT.mk «$fresh_typeId») := by
  exact freshStateRefinesOfHolds fuel cfg hguard ctx internal hfenv hdecl

/-- info: 'P4SpecTecTest.StateGeneratedRefinement.emittedFreshRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms emittedFreshRefines

private def globals : Ctx.global := {
  ftbl := ({} : Std.HashMap String Runtime.Dynamic_al.Func.t).insert
    "fresh_typeId" (.Builtin [] [] (Q.t .TextT)) }
private def cfg : Interp.Config StateEval := { guard := false }
private def call (fuel : Nat) : StateEval value :=
  Interp.do_eval_func fuel cfg globals "fresh_typeId" [] []

theorem fixtureRefines (fuel : Nat) :
    StateRefines Rel (call fuel) (ExceptT.mk «$fresh_typeId») := by
  apply emittedFreshRefines fuel cfg rfl (Ctx.empty globals) false rfl
  change Holds globals declaration
  simp [Holds, globals, declaration]

/-- info: 'P4SpecTecTest.StateGeneratedRefinement.fixtureRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fixtureRefines

theorem failureRefines (fuel : Nat) (failure : Fail) :
    StateRefines (fun (_ : value) (_ : ByteText) => False)
      (do let _ ← call fuel; throw failure)
      (do let _ ← ExceptT.mk «$fresh_typeId»; throw failure) := by
  apply stateRefinesBind (fixtureRefines fuel)
  intro _ _ _
  exact stateRefinesThrow _ failure

/-- info: 'P4SpecTecTest.StateGeneratedRefinement.failureRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms failureRefines

theorem emittedRetryRefines (fuel : Nat) :
    StateRefines Rel
      (StateEval.orElse (do let _ ← call fuel; throw .unmatch) (call fuel))
      (StateEval.orElse (do let _ ← ExceptT.mk «$fresh_typeId»; throw .unmatch)
        (ExceptT.mk «$fresh_typeId»)) := by
  apply stateRefinesOrElse ?_ (fixtureRefines fuel)
  apply stateRefinesBind (fixtureRefines fuel)
  intro _ _ _
  exact stateRefinesThrow _ .unmatch

/-- info: 'P4SpecTecTest.StateGeneratedRefinement.emittedRetryRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms emittedRetryRefines

theorem negativeRefines (fuel : Nat) :
    StateRefines (fun _ _ => True)
      (StateEval.notHold (do let _ ← call fuel; throw (α := value) .unmatch))
      (StateEval.notHold
        (do let _ ← ExceptT.mk «$fresh_typeId»; throw (α := ByteText) .unmatch)) :=
  stateRefinesNotHold (failureRefines fuel .unmatch)

/-- info: 'P4SpecTecTest.StateGeneratedRefinement.negativeRefines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms negativeRefines

-- Reset the actual emitted definition's input state. Even an indiscriminate
-- value relation must reject this change because the final states differ.
private def resetEmitted : StateEval ByteText := ExceptT.mk fun _ => «$fresh_typeId» 0

theorem resetEmittedRejected : ¬ StateRefines (fun (_ : value) (_ : ByteText) => True)
    (call 3) resetEmitted := by
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

/-- info: 'P4SpecTecTest.StateGeneratedRefinement.resetEmittedRejected' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resetEmittedRejected

end P4SpecTecTest.StateGeneratedRefinement
