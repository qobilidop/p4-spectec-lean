import P4SpecTec.Refine.StateInterp

/-!
State-preserving normalization for generated refinement proofs. In particular,
lifting pure helper computations distributes over bind without moving allocation
or rolling back either failure kind.
-/

namespace P4SpecTec.Refine

open P4SpecTec.Prelude P4SpecTec.Interp_al

/-- The interpreter's stateful helper lift is the explicit embedding. -/
theorem liftState (a : Eval α) : (liftM a : StateEval α) = StateEval.liftEval a := rfl

/-- info: 'P4SpecTec.Refine.liftState' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms liftState

/-- State-specialized effect choice is ordered stateful choice. -/
theorem orElseState (a b : StateEval α) :
    Effects.orElse a b = StateEval.orElse a b := rfl

/-- info: 'P4SpecTec.Refine.orElseState' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms orElseState

/-- Generated choice uses the same ordered stateful operation. -/
theorem hOrElseState (a b : StateEval α) : (a <|> b) = StateEval.orElse a b := rfl

/-- info: 'P4SpecTec.Refine.hOrElseState' does not depend on any axioms -/
#guard_msgs in #print axioms hOrElseState

/-- Embedding a pure failure keeps its failure tag and the current state. -/
theorem liftStateThrow (e : Fail) :
    StateEval.liftEval (throw e : Eval α) = (throw e : StateEval α) := rfl

/-- info: 'P4SpecTec.Refine.liftStateThrow' does not depend on any axioms -/
#guard_msgs in #print axioms liftStateThrow

/-- Pure helper sequencing can be normalized without touching the state. -/
theorem liftStateBind (a : Eval α) (k : α → Eval β) :
    StateEval.liftEval (a >>= k) =
      (StateEval.liftEval a >>= fun x => StateEval.liftEval (k x)) := by
  funext s
  simp only [StateEval.liftEval, Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk,
    StateT.bind, Pure.pure, Option.bind]
  cases a with
  | none => rfl
  | some r => cases r <;> rfl

/-- info: 'P4SpecTec.Refine.liftStateBind' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms liftStateBind

/-- Divergence cannot reach a continuation. -/
theorem stateDivergeBind (k : α → StateEval β) :
    (StateEval.liftEval Eval.diverge >>= k) = StateEval.liftEval Eval.diverge := rfl

/-- info: 'P4SpecTec.Refine.stateDivergeBind' does not depend on any axioms -/
#guard_msgs in #print axioms stateDivergeBind

/-- Both failure kinds stop sequencing without discarding state. -/
theorem stateThrowBind (e : Fail) (k : α → StateEval β) :
    ((throw e : StateEval α) >>= k) = throw e := rfl

/-- info: 'P4SpecTec.Refine.stateThrowBind' does not depend on any axioms -/
#guard_msgs in #print axioms stateThrowBind

/-- A bare mismatch retries at the unchanged current state. -/
theorem stateOrElseUnmatch (b : StateEval α) :
    StateEval.orElse (throw .unmatch) b = b := rfl

/-- info: 'P4SpecTec.Refine.stateOrElseUnmatch' does not depend on any axioms -/
#guard_msgs in #print axioms stateOrElseUnmatch

/-- A final mismatch adds no observable behavior, including after consumed state. -/
theorem stateOrElseUnmatchRight (a : StateEval α) :
    StateEval.orElse a (throw .unmatch) = a := by
  funext s
  change StateEval.run (StateEval.orElse a (throw .unmatch)) s = StateEval.run a s
  rw [StateEval.run_orElse]
  cases StateEval.run a s with
  | none => rfl
  | some p => rcases p with ⟨r, t⟩; cases r with
    | ok x => rfl
    | error e => cases e <;> rfl

/-- info: 'P4SpecTec.Refine.stateOrElseUnmatchRight' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms stateOrElseUnmatchRight

/-- Rewrapping a generated carrier is transparent. -/
theorem stateMkRun (a : StateEval α) : ExceptT.mk (ExceptT.run a) = a := rfl

/-- info: 'P4SpecTec.Refine.stateMkRun' does not depend on any axioms -/
#guard_msgs in #print axioms stateMkRun

/-- The emitted explicit state lambda is the same stateful computation. -/
theorem stateRunEta (a : StateEval α) :
    (ExceptT.mk fun s => StateEval.run a s) = a := rfl

/-- info: 'P4SpecTec.Refine.stateRunEta' does not depend on any axioms -/
#guard_msgs in #print axioms stateRunEta

/-- A named generated expression is introduced with its defining equality. -/
theorem stateRefinesHave {P : α → β → Prop} {m : StateEval α}
    {x : γ} {k : γ → StateEval β}
    (h : ∀ y, y = x → StateRefines P m (k y)) : StateRefines P m (let y := x; k y) :=
  h x rfl

/-- info: 'P4SpecTec.Refine.stateRefinesHave' depends on axioms: [propext] -/
#guard_msgs in #print axioms stateRefinesHave

end P4SpecTec.Refine
