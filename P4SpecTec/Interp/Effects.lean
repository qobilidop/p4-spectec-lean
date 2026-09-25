import P4SpecTec.Prelude.StateEval
import P4SpecTec.Interface.Builtin.Call

/-!
The AL interpreter's effect interface (not a mirror). One evaluator is
specialized to pure `Eval` or explicit-state `StateEval`; pure context and
value helpers are lifted transparently. No mutable state, cache registration,
deterministic-mode checking, or failure traces are added here.
-/

namespace P4SpecTec.Interp_al

open P4SpecTec.Prelude P4SpecTec.Lang.Il P4SpecTec.Runtime

/-- Operations whose interpretation differs between pure and stateful execution. -/
class Effects (m : Type → Type) extends Monad m, MonadLift Eval m where
  /-- Sequential choice retries only on mismatch. -/
  orElse : {α : Type} → m α → m α → m α
  /-- Negation flips success and mismatch without rolling back effects. -/
  notHold : {α : Type} → m α → m Unit
  /-- Dispatch an interface builtin with the current print configuration. -/
  builtin : P4.Unparse.HEnv → String → List typ → List value → m value
  /-- Observe an already computed result, once at the actual execution state. -/
  trace : {α : Type} → String → m α → m α

namespace Effects

/-- The outcome label used by the interpreter's diagnostic trace. -/
def outcome (r : Option (Except Fail α)) : String :=
  match r with
  | some (.ok _) => "ok"
  | some (.error .err) => "err"
  | some (.error .unmatch) => "unmatch"
  | none => "diverge"

/-- The checked pure builtin boundary: printer/text operation errors are hard;
arity mismatches and unsupported operations remain retryable. Other builtin
families retain the dispatcher's legacy classification. -/
def builtinEval (hints : P4.Unparse.HEnv) (name : String) (targs : List typ)
    (args : List value) : Eval value :=
  match Builtin.Call.invokeWithHints hints name targs args with
  | .ok (some v) => pure v
  | .ok none => throw .unmatch
  | .error _ => throw .err

/-- Stateful fresh dispatch checks both arities before touching the counter.
Other builtins are the unchanged pure dispatcher. Upstream cache registration
is omitted, as are the interpreter caches that consume that registration. -/
def builtinState (hints : P4.Unparse.HEnv) (name : String) (targs : List typ)
    (args : List value) : StateEval value := do
  if name == "fresh_typeId" then
    if !targs.isEmpty || !args.isEmpty then throw .unmatch
    pure (Value.Make.text (ByteText.ofString (← StateEval.freshTypeId)))
  else
    StateEval.liftEval (builtinEval hints name targs args)

/-- The original pure carrier, with identity lifting of existing helpers. -/
@[default_instance]
instance instEffectsEval : Effects Eval where
  toMonad := inferInstance
  monadLift := id
  orElse := Eval.orElse
  notHold := Eval.notHold
  builtin := builtinEval
  trace := fun label result => dbgTrace s!"{label}: {outcome result.run}" fun _ => result

/-- The explicit-state carrier retains state on all terminating outcomes.
Tracing stores the actual result before observing it; it never runs the
computation again or substitutes a fresh initial state. -/
instance instEffectsStateEval : Effects StateEval where
  toMonad := inferInstance
  monadLift := StateEval.liftEval
  orElse := StateEval.orElse
  notHold := StateEval.notHold
  builtin := builtinState
  trace := fun label computation => ExceptT.mk fun s =>
    let result := StateEval.run computation s
    dbgTrace s!"{label}: {outcome (result.map Prod.fst)}" fun _ => result

/-- The pure specialization removes helper lifts definitionally. -/
theorem liftPure (a : Eval α) : (liftM a : Eval α) = a := rfl

/-- info: 'P4SpecTec.Interp_al.Effects.liftPure' does not depend on any axioms -/
#guard_msgs in #print axioms liftPure

/-- Pure effect choice is the original evaluation operation. -/
theorem orElsePure (a b : Eval α) : Effects.orElse a b = Eval.orElse a b := rfl

/-- info: 'P4SpecTec.Interp_al.Effects.orElsePure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms orElsePure

/-- Pure effect negation is the original evaluation operation. -/
theorem notHoldPure (a : Eval α) : Effects.notHold a = Eval.notHold a := rfl

/-- info: 'P4SpecTec.Interp_al.Effects.notHoldPure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms notHoldPure

/-- Stateful tracing preserves the exact result observed at the supplied state. -/
theorem traceStateRun (label : String) (a : StateEval α) (s : FreshState) :
    StateEval.run (Effects.trace label a) s = StateEval.run a s := rfl

/-- info: 'P4SpecTec.Interp_al.Effects.traceStateRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms traceStateRun

/-- Ordered backtracking shared by both interpreter specializations. -/
def chooseSequential [Effects m] : List (Unit → m α) → m α
  | [] => monadLift (throw .unmatch : Eval α)
  | f :: fs => Effects.orElse (f ()) (chooseSequential fs)

end Effects
end P4SpecTec.Interp_al
