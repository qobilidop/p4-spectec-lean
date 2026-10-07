import P4SpecTec.Runtime.Value.Value
import P4SpecTec.Runtime.Sim.Io

/-!
Port of `p4spec/lib/backend-sim/state.ml`: the state monad of a pipeline driver, over the
current evaluation context, the architecture and the transmissions so far, with a failure
(`None`) that keeps the state. Upstream's state actions are pure; here the state threads
through the target's effect carrier `m`, since every spec callback runs in it (and, for
full P4, consumes fresh identifiers). A failed callback is the carrier's failure, not the
state monad's `None`, exactly as upstream's exception escapes its `option`.
-/

namespace P4SpecTec.BackendSim.State

open P4SpecTec.Lang.Il

/-- Mirrors `s`: context, architecture, transmissions (most recent first). -/
abbrev s := value × value × List Runtime.Sim.Io.tx

/-- Mirrors `'a state`, in the effect carrier. -/
def State (m : Type → Type) (α : Type) := s → m (Option α × s)

variable {m : Type → Type} [Monad m]

instance : Monad (State m) where
  pure a := fun s => pure (some a, s)
  bind x f := fun s => do
    let (r, s) ← x s
    match r with
    | some a => f a s
    | none => pure (none, s)

/-- Mirrors `get`. -/
def get : State m s := fun s => pure (some s, s)

/-- Mirrors `put`. -/
def put (x : s) : State m Unit := fun _ => pure (some (), x)

/-- Mirrors `modify`. -/
def modify (f : s → s) : State m Unit := fun s => pure (some (), f s)

/-- Mirrors `( >> )`. -/
def andThen {α β : Type} (ma : State m α) (mb : State m β) : State m β := ma >>= fun _ => mb

/-- Mirrors `sequence`. -/
def sequence {α : Type} : List (State m α) → State m (List α)
  | [] => pure []
  | x :: xs => do
    let a ← x
    let rest ← sequence xs
    pure (a :: rest)

/-- Mirrors `on_result`: run `some` on a result and `none` on a failure, from the state the
first computation left. -/
def on_result {α β : Type} (x : State m α) (some_ : α → State m β) (none_ : Unit → State m β) :
    State m β := fun s => do
  let (r, s') ← x s
  match r with
  | some a => some_ a s'
  | none => none_ () s'

/-- Mirrors `apply`: a function of the context and architecture that returns both updated
and a result. -/
def apply {α : Type} (f : value → value → m (value × value × α)) : State m α := fun s => do
  let (value_ctx, value_arch, txs) := s
  let (value_ctx, value_arch, result) ← f value_ctx value_arch
  pure (some result, (value_ctx, value_arch, txs))

/-- Lift a carrier computation. -/
def lift {α : Type} (x : m α) : State m α := fun s => do pure (some (← x), s)

/-- Mirrors `guard`. -/
def guard (cond : Bool) : State m Unit := fun s => pure (if cond then some () else none, s)

/-- Mirrors `empty`. -/
def empty {α : Type} : State m α := fun s => pure (none, s)

/-- Mirrors `run`. -/
def run {α : Type} (x : State m α) (st : s) : m (Option α × s) := x st

end P4SpecTec.BackendSim.State
