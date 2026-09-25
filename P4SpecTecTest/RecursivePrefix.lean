import P4SpecTec.Refine.StateCalc

/-!
A bounded mutually recursive proof experiment. A rejected attempt calls
the same SCC and consumes fresh state before the selected structural rule.
The successful relation is not the run graph. No generator support is claimed.
-/

namespace P4SpecTecTest.RecursivePrefix

open P4SpecTec.Prelude P4SpecTec.Refine

mutual

def walk (n : Nat) (s : FreshState) :
    Option (Except Fail (List String) × FreshState) :=
  StateEval.run ((ExceptT.mk (reject n) : StateEval (List String)) <|>
    (match n with
    | 0 => pure []
    | n + 1 => do
      let x ← StateEval.freshTypeId
      let xs ← (ExceptT.mk (walk n) : StateEval (List String))
      pure (x :: xs))) s
partial_fixpoint

def reject (n : Nat) (s : FreshState) :
    Option (Except Fail (List String) × FreshState) :=
  StateEval.run (do
    let _ ← StateEval.freshTypeId
    match n with
    | 0 => throw .unmatch
    | n + 1 =>
      let _ ← (ExceptT.mk (walk n) : StateEval (List String))
      throw .unmatch) s
partial_fixpoint

end

/-- info: 'P4SpecTecTest.RecursivePrefix.walk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms walk

/-- info: 'P4SpecTecTest.RecursivePrefix.reject' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reject

inductive Walk : Nat → FreshState → List String → FreshState → Prop where
  | nil {s u} : RejectedPrefix [ExceptT.mk (reject 0)] s u → Walk 0 s [] u
  | cons {n s u xs t} : RejectedPrefix [ExceptT.mk (reject (n + 1))] s u →
      Walk n u.next xs t →
      Walk (n + 1) s (("FRESH__" ++ toString u.counter) :: xs) t

/-- Identity refinement transports the entire terminating pair, not only success. -/
theorem transport {a b : StateEval α} (h : StateRefines Eq a b)
    {s : FreshState} {r : Except Fail α × FreshState}
    (hr : StateEval.run a s = some r) : StateEval.run b s = some r := by
  rcases r with ⟨r, t⟩
  obtain ⟨r', hb, he⟩ := h s r t hr
  have eq : r = r' := by
    cases r <;> cases r' <;> simp_all [ResRel]
  cases eq
  exact hb

/-- info: 'P4SpecTecTest.RecursivePrefix.transport' depends on axioms: [propext] -/
#guard_msgs in #print axioms transport

/-- Operational realization of recursive approximants supplies identity refinement. -/
theorem realization {a b : FreshState → Option (Except Fail α × FreshState)}
    (h : ∀ s r, a s = some r → b s = some r) :
    StateRefines Eq (ExceptT.mk a) (ExceptT.mk b) := by
  intro s r t hr
  exact ⟨r, h s (r, t) hr, by cases r <;> rfl⟩

/-- info: 'P4SpecTecTest.RecursivePrefix.realization' depends on axioms: [propext] -/
#guard_msgs in #print axioms realization

def tailBody (f : Nat → FreshState → Option (Except Fail (List String) × FreshState))
    (n : Nat) : StateEval (List String) :=
  match n with
  | 0 => pure []
  | n + 1 => do
    let x ← StateEval.freshTypeId
    let xs ← (ExceptT.mk (f n) : StateEval (List String))
    pure (x :: xs)

theorem tailRefinement
    {f g : Nat → FreshState → Option (Except Fail (List String) × FreshState)}
    (h : ∀ n, StateRefines Eq (ExceptT.mk (f n)) (ExceptT.mk (g n))) (n : Nat) :
    StateRefines Eq (tailBody f n) (tailBody g n) := by
  cases n with
  | zero => exact stateRefinesRefl _
  | succ n =>
    apply stateRefinesBind (stateRefinesRefl _)
    intro x y he
    cases he
    apply stateRefinesBind (h n)
    intro xs ys he
    cases he
    exact stateRefinesRefl _

/-- info: 'P4SpecTecTest.RecursivePrefix.tailRefinement' depends on axioms: [propext] -/
#guard_msgs in #print axioms tailRefinement

/-- A stronger SCC motive preserves failed recursive calls and structural successes. -/
theorem walkSound (n : Nat) (s : FreshState) (xs : List String) (t : FreshState)
    (h : walk n s = some (.ok xs, t)) : Walk n s xs t := by
  have all := walk.partial_correctness
    (motive_1 := fun n s r => walk n s = some r ∧
      ∀ xs t, r = (.ok xs, t) → Walk n s xs t)
    (motive_2 := fun n s r => reject n s = some r ∧ ∀ xs, r.1 ≠ .ok xs)
    (by
      intro recWalk recReject ihWalk ihReject n s r hr
      have hrw (n) := realization (fun s r h => (ihWalk n s r h).1)
      have hrr (n) := realization (fun s r h => (ihReject n s r h).1)
      have tailRef := tailRefinement hrw n
      constructor
      · rw [walk.eq_def]
        exact transport (stateRefinesOrElse (hrr n) tailRef) hr
      · intro xs t he
        cases he
        change StateEval.run (StateEval.orElse _ _) s = some (.ok xs, t) at hr
        rw [StateEval.run_orElse] at hr
        dsimp only [StateEval.run, ExceptT.run, ExceptT.mk] at hr
        cases hj : recReject n s with
        | none => simp [hj] at hr
        | some result =>
          rcases result with ⟨result, u⟩
          have hjReal := ihReject n s (result, u) hj
          cases result with
          | ok v => exact False.elim (hjReal.2 v rfl)
          | error e =>
            cases e with
            | err => simp [hj] at hr
            | unmatch =>
              simp only [hj] at hr
              have hprefix : RejectedPrefix [ExceptT.mk (reject n)] s u :=
                .cons hjReal.1 (.nil u)
              cases n with
              | zero => cases hr; exact .nil hprefix
              | succ n =>
                obtain ⟨ys, w, hy, hend⟩ := (StateEval.runBindOk _ _ _ _ _).mp hr
                simp only [StateEval.runPure, Option.some.injEq, Prod.mk.injEq,
                  Except.ok.injEq] at hend
                rcases hend with ⟨rfl, rfl⟩
                exact .cons hprefix ((ihWalk n u.next (.ok ys, w) hy).2 ys w rfl))
    (by
      intro recWalk ihWalk n s r hr
      have hrw (n) := realization (fun s r h => (ihWalk n s r h).1)
      constructor
      · rw [reject.eq_def]
        apply transport (b := (do
          let _ ← StateEval.freshTypeId
          match n with
          | 0 => throw .unmatch
          | n + 1 =>
            let _ ← (ExceptT.mk (walk n) : StateEval (List String))
            throw .unmatch)) ?_ hr
        apply stateRefinesBind (stateRefinesRefl _)
        intro x y he
        cases he
        cases n with
        | zero => exact stateRefinesRefl _
        | succ n =>
          apply stateRefinesBind (hrw n)
          intro xs ys he
          cases he
          exact stateRefinesRefl _
      · rw [StateEval.runBind, StateEval.run_freshTypeId] at hr
        simp only [Option.bind_some] at hr
        cases n with
        | zero => cases hr; intro xs he; cases he
        | succ n =>
          rw [StateEval.runBind] at hr
          cases hc : recWalk n s.next with
          | none => simp [StateEval.run, hc] at hr
          | some result =>
            rcases result with ⟨result, u⟩
            cases result <;> simp [StateEval.run, hc] at hr <;>
              cases hr <;> intro xs he <;> cases he)
    n s (.ok xs, t) h
  exact all.2 xs t rfl

/-- info: 'P4SpecTecTest.RecursivePrefix.walkSound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms walkSound

local instance [BEq α] : BEq (Except Fail α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

-- The rejecting callee itself recurses before returning its consumed state.
#guard reject 0 0 == some (.error .unmatch, FreshState.ofInt 1)
#guard reject 1 0 == some (.error .unmatch, FreshState.ofInt 2)
#guard reject 2 0 == some (.error .unmatch, FreshState.ofInt 5)
#guard walk 0 0 == some (.ok [], FreshState.ofInt 1)
#guard walk 1 0 == some (.ok ["FRESH__2"], FreshState.ofInt 4)
#guard walk 2 0 == some (.ok ["FRESH__5", "FRESH__8"], FreshState.ofInt 10)
#guard walk 1 (FreshState.ofInt 4611686018427387903) ==
  some (.ok ["FRESH__-4611686018427387903"], FreshState.ofInt (-4611686018427387901))

-- Graph realization includes hard errors, even though this fixture's final
-- definitions happen to terminate only with success or mismatch.
theorem hardErrorTransport (s : FreshState) :
    StateEval.run (throw .err : StateEval (List String)) s = some (.error .err, s) :=
  transport (stateRefinesRefl _) rfl

/-- info: 'P4SpecTecTest.RecursivePrefix.hardErrorTransport' depends on axioms: [propext] -/
#guard_msgs in #print axioms hardErrorTransport

end P4SpecTecTest.RecursivePrefix
