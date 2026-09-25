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

open Lean.Order

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

/-! ## Transparent execution and recursion support -/

/-- Executing a pure return does not change state. -/
theorem runPure (a : α) (s : FreshState) :
    run (pure a) s = some (.ok a, s) := rfl

/-- info: 'P4SpecTec.Prelude.StateEval.runPure' does not depend on any axioms -/
#guard_msgs in #print axioms runPure

/-- Throwing either failure preserves the current state. -/
theorem runThrow (e : Fail) (s : FreshState) :
    run (throw e : StateEval α) s = some (.error e, s) := rfl

/-- info: 'P4SpecTec.Prelude.StateEval.runThrow' does not depend on any axioms -/
#guard_msgs in #print axioms runThrow

/-- Bind passes successful post-state to the continuation and retains it
when propagating either failure. -/
theorem runBind (m : StateEval α) (k : α → StateEval β) (s : FreshState) :
    run (m >>= k) s = (run m s).bind (fun (r, t) =>
      match r with
      | .ok a => run (k a) t
      | .error e => some (.error e, t)) := by
  cases h : m s with
  | none => simp [run, ExceptT.run, ExceptT.mk, Bind.bind, ExceptT.bind, StateT.bind, h]
  | some v =>
    rcases v with ⟨r, t⟩
    cases r <;> simp [run, ExceptT.run, ExceptT.mk, Bind.bind, ExceptT.bind, StateT.bind,
      ExceptT.bindCont, Pure.pure, StateT.pure, h]

/-- info: 'P4SpecTec.Prelude.StateEval.runBind' depends on axioms: [propext] -/
#guard_msgs in #print axioms runBind

/-- Successful bind exposes an intermediate value and its precise state. -/
theorem runBindOk (m : StateEval α) (k : α → StateEval β) (s t : FreshState) (b : β) :
    run (m >>= k) s = some (.ok b, t) ↔
      ∃ a u, run m s = some (.ok a, u) ∧ run (k a) u = some (.ok b, t) := by
  rw [runBind]
  cases h : run m s with
  | none => simp
  | some v =>
    rcases v with ⟨r, u⟩
    cases r with
    | error e => simp
    | ok a =>
      simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq, Except.ok.injEq]
      constructor
      · intro hk; exact ⟨a, u, ⟨rfl, rfl⟩, hk⟩
      · rintro ⟨a', u', ⟨rfl, rfl⟩, hk⟩; exact hk

/-- info: 'P4SpecTec.Prelude.StateEval.runBindOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runBindOk

/-- Running the carrier at a fixed state preserves monotonicity. -/
@[partial_fixpoint_monotone]
theorem monotoneRun {γ α : Type} [PartialOrder γ] (f : γ → StateEval α)
    (hf : monotone f) (s : FreshState) :
    monotone (fun x => run (f x) s) := fun x y h => hf x y h s

/-- info: 'P4SpecTec.Prelude.StateEval.monotoneRun' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms monotoneRun

/-- The stateful carrier wrapper is monotone. -/
@[partial_fixpoint_monotone]
theorem monotoneMk {γ α : Type} [PartialOrder γ]
    (f : γ → FreshState → Option (Except Fail α × FreshState)) (hf : monotone f) :
    monotone (fun x => (ExceptT.mk (f x) : StateEval α)) := hf

/-- info: 'P4SpecTec.Prelude.StateEval.monotoneMk' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms monotoneMk

/-- Sequential choice is monotone in both alternatives, at every state. -/
@[partial_fixpoint_monotone]
theorem monotoneOrElse {γ α : Type} [PartialOrder γ] (f g : γ → StateEval α)
    (hf : monotone f) (hg : monotone g) : monotone (fun x => orElse (f x) (g x)) := by
  apply monotone_of_monotone_apply
  intro s
  change monotone (fun x => (run (f x) s) >>= fun (r, t) =>
    match r with
    | .ok a => some (.ok a, t)
    | .error .err => some (.error .err, t)
    | .error .unmatch => run (g x) t)
  apply monotone_bind Option
  · exact monotoneRun f hf s
  · apply monotone_of_monotone_apply
    intro (r, t)
    cases r with
    | ok a => apply monotone_const
    | error e => cases e with
      | err => apply monotone_const
      | unmatch => exact monotoneRun g hg t

/-- info: 'P4SpecTec.Prelude.StateEval.monotoneOrElse' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms monotoneOrElse

/-- The notation for sequential choice has the same monotonicity. -/
@[partial_fixpoint_monotone]
theorem monotoneHOrElse {γ α : Type} [PartialOrder γ] (f g : γ → StateEval α)
    (hf : monotone f) (hg : monotone g) : monotone (fun x => (f x <|> g x)) :=
  monotoneOrElse f g hf hg

/-- info: 'P4SpecTec.Prelude.StateEval.monotoneHOrElse' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms monotoneHOrElse

/-- Negation is monotone, including when its operand consumes state. -/
@[partial_fixpoint_monotone]
theorem monotoneNotHold {γ α : Type} [PartialOrder γ] (f : γ → StateEval α)
    (hf : monotone f) : monotone (fun x => notHold (f x)) := by
  apply monotone_of_monotone_apply
  intro s
  change monotone (fun x => (run (f x) s) >>= fun (r, t) =>
    match r with
    | .ok _ => some (Except.error (α := Unit) .unmatch, t)
    | .error .err => some (Except.error (α := Unit) .err, t)
    | .error .unmatch => some (Except.ok (ε := Fail) (), t))
  apply monotone_bind Option
  · exact monotoneRun f hf s
  · apply monotone_const

/-- info: 'P4SpecTec.Prelude.StateEval.monotoneNotHold' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms monotoneNotHold

end StateEval
end P4SpecTec.Prelude
