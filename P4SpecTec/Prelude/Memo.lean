import P4SpecTec.Prelude.StateEval
import Lean.Data.PersistentHashMap

/-!
Memoized execution of explicit-state computations: upstream's cache mode, as a
semantics-transparent optimization of the executable.

Upstream's AL interpreter runs with a cache of relation and function results (`cache=true`
in its test configuration), keyed by the callee and its input values, filled only when the
call made no side effect on the fresh-identifier counter. Without it, a rule group whose
earlier rules evaluate a recursive premise before failing late, such as `TableKeys_eval`'s
`cons-head-cont-tail-exit`, costs time exponential in the list's length, because every
later rule evaluates the same premises again from the same state.

`memoRun name keys x` is `x` by definition: proofs see no cache. Its compiled implementation
memoizes: a key is the identity of each input object (the objects stay referenced by the
entry, so an address names one value for as long as the entry lives), with the initial
counter; an entry is written only for a run that succeeded without moving the counter, so
the result of a hit is the result the computation itself would have produced from that
state. `memoRunBounded` adds a fuel bound: a run that succeeded under a bound succeeds
identically under any larger one, so a hit needs a bound at least the stored one. A miss,
a failure or an allocation runs the computation. The cache is bounded and cleared when
full (upstream evicts by a clock instead).

The table is process-wide and keyed by the callee's name, so one process must run one
semantics per name: one extern implementation and one spec. The callers keep that: the
generated library's names are the AL identifiers, the interpreter prefixes its own, and
every oracle process runs a single target.

The table lives in a cell initialized with the module, which the runtime treats as shared
between threads: nothing stored in it is ever exclusive, so an insertion into a flat hash
map would copy its whole bucket array. A persistent hash map copies only the path to the
changed leaf.
-/

namespace P4SpecTec.Prelude

/-- An input's identity for memoization. Logically no information; the compiled `MemoKey.of`
keeps the input object itself. Two fields, so that the runtime never unboxes it. -/
inductive MemoKey where
  /-- The only constructor. -/
  | mk (a b : Nat)

/-- The runtime key: the object itself, by reference. -/
unsafe def MemoKey.ofImpl {β : Type} (b : β) : MemoKey := unsafeCast b

/-- The key of an input, logically constant. -/
@[implemented_by MemoKey.ofImpl]
def MemoKey.of {β : Type} (_ : β) : MemoKey := .mk 0 0

/-- The address key of a call: callee, input identities and initial counter. -/
abbrev MemoAddress := String × List USize × Int

/-- The cache: its entry count, and address keys to the inputs (kept alive), the bound
the run had, and the boxed result. -/
abbrev MemoTable := Nat × Lean.PersistentHashMap MemoAddress (List MemoKey × Nat × NonScalar)

/-- Entries beyond this count clear the cache; upstream's caches hold 256K entries. -/
def memoCapacity : Nat := 262144

/-- The process-wide cache. -/
initialize memoTable : IO.Ref MemoTable ← IO.mkRef (0, {})

/-- The cached result under a key whose objects are the given ones and whose run had at
most the given bound. -/
@[noinline] unsafe def lookup (key : MemoAddress) (keys : List MemoKey) (bound : Nat) :
    BaseIO (Option NonScalar) := do
  let (_, table) ← memoTable.get
  match table.find? key with
  | some (objects, stored, boxed) =>
    if stored ≤ bound && objects.length == keys.length &&
        (objects.zip keys).all fun (a, b) => ptrEq a b then
      pure (some boxed)
    else pure none
  | none => pure none

/-- Record a result, or start over when the table is full. -/
@[noinline] unsafe def store (key : MemoAddress) (keys : List MemoKey) (bound : Nat)
    (boxed : NonScalar) : BaseIO Unit :=
  memoTable.modify fun (count, table) =>
    if count ≥ memoCapacity then
      (1, ({} : Lean.PersistentHashMap _ _).insert key (keys, bound, boxed))
    else (count + 1, table.insert key (keys, bound, boxed))

/-- The memoizing implementation. -/
unsafe def memoRunImpl {α : Type} (name : String) (keys : List MemoKey) (bound : Nat)
    (x : StateEval α) : StateEval α :=
  ExceptT.mk fun s => unsafeBaseIO do
    let key := (name, keys.map fun k => ptrAddrUnsafe k, s.counter)
    if let some boxed ← lookup key keys bound then
      return (unsafeCast boxed : Option (Except Fail α × FreshState))
    let result := StateEval.run x s
    if let some (.ok _, s') := result then
      if s' == s then store key keys bound (unsafeCast result : NonScalar)
    return result

/-- The implementation without a bound. -/
unsafe def memoRunImpl0 {α : Type} (name : String) (keys : List MemoKey) (x : StateEval α) :
    StateEval α := memoRunImpl name keys 0 x

/-- Run `x`, by definition; executed through the cache. -/
@[implemented_by memoRunImpl0]
def memoRun {α : Type} (_name : String) (_keys : List MemoKey) (x : StateEval α) :
    StateEval α := x

/-- Run `x` under a fuel bound, by definition; executed through the cache, where a hit's
run had a bound at most this one. -/
@[implemented_by memoRunImpl]
def memoRunBounded {α : Type} (_name : String) (_keys : List MemoKey) (_bound : Nat)
    (x : StateEval α) : StateEval α := x

/-- Memoization is the computation itself. -/
@[simp] theorem memoRun_eq {α : Type} (name : String) (keys : List MemoKey) (x : StateEval α) :
    memoRun name keys x = x := rfl

/-- info: 'P4SpecTec.Prelude.memoRun_eq' does not depend on any axioms -/
#guard_msgs in #print axioms memoRun_eq

/-- Bounded memoization is the computation itself. -/
@[simp] theorem memoRunBounded_eq {α : Type} (name : String) (keys : List MemoKey) (bound : Nat)
    (x : StateEval α) : memoRunBounded name keys bound x = x := rfl

/-- info: 'P4SpecTec.Prelude.memoRunBounded_eq' does not depend on any axioms -/
#guard_msgs in #print axioms memoRunBounded_eq

open Lean.Order in
/-- Memoization preserves monotonicity, so a relation's fixed point may call through it. -/
@[partial_fixpoint_monotone]
theorem monotoneMemoRun {γ α : Type} [PartialOrder γ] (name : String) (keys : List MemoKey)
    (f : γ → StateEval α) (hf : monotone f) : monotone (fun x => memoRun name keys (f x)) := hf

/-- info: 'P4SpecTec.Prelude.monotoneMemoRun' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms monotoneMemoRun

end P4SpecTec.Prelude
