import P4SpecTec.Prelude.Eval
import Init.Data.BitVec.Basic

/-!
An explicit-state foundation for upstream's fresh identifiers. This is an
experiment, not yet the monad of generated code or of the AL interpreter.
The allocation operation follows `interface/builtin/fresh.ml`; choice and
negation follow `interp/interp-al/{backtrack,interp}.ml` at the upstream pin.

Upstream's counter is an OCaml `int`: on the project's 64-bit platforms it
has 63 signed bits and wraps. State sits below failure, so failed branches
retain allocations. `StateT FreshState Eval` would instead lose the state
on failure. Divergence (`none`) has no observable final state.
-/

namespace P4SpecTec.Prelude

/-- The bit pattern of a 63-bit OCaml counter on a 64-bit host. -/
abbrev FreshState := BitVec 63

namespace FreshState

/-- A fresh upstream process starts with this counter. Running a computation
does not implicitly reset it; callers explicitly retain or replace state. -/
def initial : FreshState := 0

/-- An explicit seed, reduced modulo the upstream counter's 63 bits. -/
def ofInt (n : Int) : FreshState := BitVec.ofInt 63 n

/-- The signed decimal value used by upstream's `string_of_int`. -/
def counter (s : FreshState) : Int := s.toInt

/-- Increment with the wraparound of a 63-bit OCaml integer. -/
def next (s : FreshState) : FreshState := s + 1

end FreshState

/-- Stateful evaluation retaining post-state on either failure kind:
`FreshState → Option (Except Fail α × FreshState)`. -/
abbrev StateEval := ExceptT Fail (StateT FreshState Option)

namespace StateEval

/-- Observe both the result and counter of a terminating computation. -/
def run (a : StateEval α) (s : FreshState) : Option (Except Fail α × FreshState) :=
  ExceptT.run a s

/-- Sequential choice retries only a mismatch, using its post-state. Errors
and successes stop; divergence cannot trigger a fallback. -/
def orElse (a b : StateEval α) : StateEval α :=
  ExceptT.mk fun s => do
    let (r, s') ← run a s
    match r with
    | .ok x => pure (.ok x, s')
    | .error .err => pure (.error .err, s')
    | .error .unmatch => run b s'

/-- Use upstream's sequential choice instead of the inherited exception
handler, which would retry on hard errors as well. -/
instance instOrElse : OrElse (StateEval α) := ⟨fun a b => orElse a (b ())⟩

/-- Negation flips success and mismatch without undoing allocations. -/
def notHold (a : StateEval α) : StateEval Unit :=
  ExceptT.mk fun s => do
    let (r, s') ← run a s
    match r with
    | .ok _ => pure (.error .unmatch, s')
    | .error .err => pure (.error .err, s')
    | .error .unmatch => pure (.ok (), s')

/-- Embed an existing pure evaluation without changing the counter, including
on failure. Pure divergence remains divergence. -/
def liftEval (a : Eval α) : StateEval α :=
  ExceptT.mk fun s => do
    let r ← ExceptT.run a
    pure (r, s)

/-- Allocate the old counter's signed decimal spelling, then increment.
This typed primitive assumes the upstream builtin's zero-argument check;
it does not model its value-cache registration callback. -/
def freshTypeId : StateEval String :=
  ExceptT.mk fun s => some (.ok ("FRESH__" ++ toString s.counter), s.next)

/-- Executing a lifted pure evaluation preserves its input state. -/
theorem run_liftEval (a : Eval α) (s : FreshState) :
    run (liftEval a) s = (ExceptT.run a).map (fun r => (r, s)) := by
  change (ExceptT.run a >>= fun r => some (r, s)) = _
  cases ExceptT.run a <;> rfl

/-- info: 'P4SpecTec.Prelude.StateEval.run_liftEval' does not depend on any axioms -/
#guard_msgs in #print axioms run_liftEval

/-- Allocation exposes exactly the old spelling and the incremented state. -/
theorem run_freshTypeId (s : FreshState) :
    run freshTypeId s = some (.ok ("FRESH__" ++ toString s.counter), s.next) := rfl

/-- info: 'P4SpecTec.Prelude.StateEval.run_freshTypeId' depends on axioms: [propext] -/
#guard_msgs in #print axioms run_freshTypeId

/-- Sequential choice observes the first result before deciding whether to
run the second computation; the latter receives the first post-state. -/
theorem run_orElse (a b : StateEval α) (s : FreshState) :
    run (orElse a b) s = (do
      let (r, s') ← run a s
      match r with
      | .ok x => some (.ok x, s')
      | .error .err => some (.error .err, s')
      | .error .unmatch => run b s') := rfl

/-- info: 'P4SpecTec.Prelude.StateEval.run_orElse' does not depend on any axioms -/
#guard_msgs in #print axioms run_orElse

/-- A mismatch retries with the consumed counter, never the input counter. -/
theorem run_orElse_unmatch (a b : StateEval α) (s s' : FreshState)
    (h : run a s = some (.error .unmatch, s')) :
    run (orElse a b) s = run b s' := by
  rw [run_orElse, h]
  rfl

/-- info: 'P4SpecTec.Prelude.StateEval.run_orElse_unmatch' does not depend on any axioms -/
#guard_msgs in #print axioms run_orElse_unmatch

/-- Negation changes only the failure/success tag, not the post-state. -/
theorem run_notHold (a : StateEval α) (s : FreshState) :
    run (notHold a) s = (do
      let (r, s') ← run a s
      match r with
      | .ok _ => some (.error .unmatch, s')
      | .error .err => some (.error .err, s')
      | .error .unmatch => some (.ok (), s')) := rfl

/-- info: 'P4SpecTec.Prelude.StateEval.run_notHold' does not depend on any axioms -/
#guard_msgs in #print axioms run_notHold

end StateEval
end P4SpecTec.Prelude
