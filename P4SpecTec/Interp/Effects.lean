import P4SpecTec.Prelude.StateEval
import P4SpecTec.Prelude.Memo
import P4SpecTec.Interface.Builtin.Call

/-!
The AL interpreter's effect interface (not a mirror). One evaluator is
specialized to pure `Eval` or explicit-state `StateEval`; pure context and
value helpers are lifted transparently. No mutable state, cache registration,
deterministic-mode checking, or failure traces are added here; the stateful carrier's
memoization of relation runs is the run by definition (`Prelude/Memo.lean`).
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
  /-- Upstream's cache mode around a defined relation's invocation, named, with the fuel it
  has and its inputs: the invocation itself, unless the carrier memoizes it. -/
  memoRel : String → Nat → List value → m (List value) → m (List value) := fun _ _ _ x => x

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
is omitted; its cache of relation results is mirrored by `memoRel` below, in the stateful
carrier only, as a semantics-transparent optimization (`Prelude/Memo.lean`). -/
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
  memoRel := fun _ _ _ x => x

/-- The memo keys of an IL value: its constructor, then the object whose identity stands
for it. For a structured value that is its payload container, which pattern binding shares
(the interpreter re-wraps a list's tail in a new `ListV`, keeping the list), and two values
with one container are `eq`, which is what upstream's cache keys by; for a scalar it is the
value itself. The constructor keeps containers of different shapes apart. Notes and regions
are not part of the key, as they are not of `eq`: a hit's outputs may carry the notes and
regions of the first caller's inputs, as upstream's cached outputs do. -/
def memoKeys (v : value) : List MemoKey :=
  match v.it with
  | .ListV vs => [MemoKey.of 0, MemoKey.of vs]
  | .TupleV vs => [MemoKey.of 1, MemoKey.of vs]
  | .StructV fields => [MemoKey.of 2, MemoKey.of fields]
  | .CaseV m => [MemoKey.of 3, MemoKey.of m]
  | .OptV (some w) => [MemoKey.of 4, MemoKey.of w]
  | _ => [MemoKey.of 5, MemoKey.of v]

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
  -- The name is prefixed so that the process-wide table never mixes the interpreter's
  -- entries with the generated library's, which share the AL identifiers.
  memoRel := fun name fuel inputs x =>
    memoRunBounded ("al:" ++ name) (inputs.flatMap memoKeys) fuel x

/-- The pure specialization removes helper lifts definitionally. -/
theorem liftPure (a : Eval α) : (liftM a : Eval α) = a := rfl

/-- info: 'P4SpecTec.Interp_al.Effects.liftPure' does not depend on any axioms -/
#guard_msgs in #print axioms liftPure

/-- Pure effect choice is the original evaluation operation. -/
theorem orElsePure (a b : Eval α) : Effects.orElse a b = Eval.orElse a b := rfl

/-- info: 'P4SpecTec.Interp_al.Effects.orElsePure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms orElsePure

/-- The pure carrier does not memoize. -/
@[simp] theorem memoRelPure (name : String) (fuel : Nat) (inputs : List value)
    (x : Eval (List value)) : Effects.memoRel name fuel inputs x = x := rfl

/-- info: 'P4SpecTec.Interp_al.Effects.memoRelPure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memoRelPure

/-- The stateful carrier's memoization is the invocation itself. -/
@[simp] theorem memoRelState (name : String) (fuel : Nat) (inputs : List value)
    (x : StateEval (List value)) : Effects.memoRel name fuel inputs x = x := rfl

/-- info: 'P4SpecTec.Interp_al.Effects.memoRelState' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memoRelState

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
