import P4SpecTec.Refine.Eval
import Batteries.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
Finite realization of generated outcomes by fuel-indexed reference computations.
An eventual witness supplies the same outcome at every sufficiently large fuel,
so separate witnesses compose at a common bound. These rules do not assume or
establish fuel stability for the AL interpreter; each application must construct
the eventual witnesses for its actual reference computations. Exhaustion remains
distinct from both failure kinds. State and observations need separate contracts.
-/

namespace P4SpecTec.Refine

open P4SpecTec.Prelude

/-- The same outcome occurs at every sufficiently large reference fuel. -/
def EventuallyRuns (m : Nat → Eval α) (r : Except Fail α) : Prop :=
  ∃ bound, ∀ fuel, bound ≤ fuel → (m fuel).run = some r

/-- Every defined generated outcome has a related eventual reference witness.
This strengthens existential reverse correspondence for compositional use. -/
def Realizes (P : α → β → Prop) (reference : Nat → Eval α) (generated : Eval β) : Prop :=
  ∀ q, generated.run = some q →
    ∃ r, EventuallyRuns reference r ∧ ResRel P r q

/-- An eventual witness supplies the finite execution required by reverse correspondence. -/
theorem EventuallyRuns.witness (h : EventuallyRuns m r) :
    ∃ fuel, (m fuel).run = some r := by
  obtain ⟨bound, hbound⟩ := h
  exact ⟨bound, hbound bound (Nat.le_refl _)⟩

/-- info: 'P4SpecTec.Refine.EventuallyRuns.witness'
does not depend on any axioms -/
#guard_msgs in #print axioms EventuallyRuns.witness

/-- A defined computation independent of fuel has an eventual witness. -/
theorem EventuallyRuns.constant {m : Eval α} (h : m.run = some r) :
    EventuallyRuns (fun _ => m) r :=
  ⟨0, fun _ _ => h⟩

/-- info: 'P4SpecTec.Refine.EventuallyRuns.constant'
does not depend on any axioms -/
#guard_msgs in #print axioms EventuallyRuns.constant

/-- Pointwise equality above a finite threshold transports an eventual witness. -/
theorem EventuallyRuns.congrAbove {m n : Nat → Eval α} (h : EventuallyRuns m r)
    (threshold : Nat) (heq : ∀ fuel, threshold ≤ fuel → n fuel = m fuel) :
    EventuallyRuns n r := by
  obtain ⟨bound, hbound⟩ := h
  refine ⟨max bound threshold, fun fuel hfuel => ?_⟩
  rw [heq fuel (Nat.le_trans (Nat.le_max_right _ _) hfuel)]
  exact hbound fuel (Nat.le_trans (Nat.le_max_left _ _) hfuel)

/-- info: 'P4SpecTec.Refine.EventuallyRuns.congrAbove'
depends on axioms: [propext] -/
#guard_msgs in #print axioms EventuallyRuns.congrAbove

/-- A fixed number of interpreter helper entries can be added to the fuel bound. -/
theorem EventuallyRuns.offset {m : Nat → Eval α} (h : EventuallyRuns m r)
    (offset : Nat) : EventuallyRuns (fun fuel => m (fuel - offset)) r := by
  obtain ⟨bound, hbound⟩ := h
  exact ⟨bound + offset, fun fuel hfuel => hbound (fuel - offset) (by omega)⟩

/-- info: 'P4SpecTec.Refine.EventuallyRuns.offset'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms EventuallyRuns.offset

/-- A successful prefix and its actual continuation combine at the maximum bound. -/
theorem EventuallyRuns.bindOk {m : Nat → Eval α} {next : Nat → α → Eval β}
    (hm : EventuallyRuns m (.ok a)) (hn : EventuallyRuns (fun fuel => next fuel a) r) :
    EventuallyRuns (fun fuel => m fuel >>= next fuel) r := by
  obtain ⟨left, hl⟩ := hm
  obtain ⟨right, hr⟩ := hn
  refine ⟨max left right, fun fuel hfuel => ?_⟩
  rw [run_bind, hl fuel (Nat.le_trans (Nat.le_max_left _ _) hfuel)]
  exact hr fuel (Nat.le_trans (Nat.le_max_right _ _) hfuel)

/-- info: 'P4SpecTec.Refine.EventuallyRuns.bindOk'
depends on axioms: [propext] -/
#guard_msgs in #print axioms EventuallyRuns.bindOk

/-- Either failure kind propagates through bind without evaluating its continuation. -/
theorem EventuallyRuns.bindError {m : Nat → Eval α} (hm : EventuallyRuns m (.error e))
    (next : Nat → α → Eval β) :
    EventuallyRuns (fun fuel => m fuel >>= next fuel) (.error e) := by
  obtain ⟨bound, hbound⟩ := hm
  refine ⟨bound, fun fuel hfuel => ?_⟩
  rw [run_bind, hbound fuel hfuel]
  rfl

/-- info: 'P4SpecTec.Refine.EventuallyRuns.bindError'
does not depend on any axioms -/
#guard_msgs in #print axioms EventuallyRuns.bindError

/-- A successful first alternative fixes the result, regardless of the second. -/
theorem EventuallyRuns.orElseOk {m : Nat → Eval α} (hm : EventuallyRuns m (.ok a))
    (other : Nat → Eval α) :
    EventuallyRuns (fun fuel => Eval.orElse (m fuel) (other fuel)) (.ok a) := by
  obtain ⟨bound, hbound⟩ := hm
  refine ⟨bound, fun fuel hfuel => ?_⟩
  rw [run_orElse, hbound fuel hfuel]
  rfl

/-- info: 'P4SpecTec.Refine.EventuallyRuns.orElseOk'
does not depend on any axioms -/
#guard_msgs in #print axioms EventuallyRuns.orElseOk

/-- A hard error stops ordered choice even if the second alternative succeeds. -/
theorem EventuallyRuns.orElseError {m : Nat → Eval α}
    (hm : EventuallyRuns m (.error .err)) (other : Nat → Eval α) :
    EventuallyRuns (fun fuel => Eval.orElse (m fuel) (other fuel)) (.error .err) := by
  obtain ⟨bound, hbound⟩ := hm
  refine ⟨bound, fun fuel hfuel => ?_⟩
  rw [run_orElse, hbound fuel hfuel]
  rfl

/-- info: 'P4SpecTec.Refine.EventuallyRuns.orElseError'
does not depend on any axioms -/
#guard_msgs in #print axioms EventuallyRuns.orElseError

/-- Retrying requires a terminating mismatch witness for the first alternative. -/
theorem EventuallyRuns.orElseUnmatch {m n : Nat → Eval α}
    (hm : EventuallyRuns m (.error .unmatch)) (hn : EventuallyRuns n r) :
    EventuallyRuns (fun fuel => Eval.orElse (m fuel) (n fuel)) r := by
  obtain ⟨left, hl⟩ := hm
  obtain ⟨right, hr⟩ := hn
  refine ⟨max left right, fun fuel hfuel => ?_⟩
  rw [run_orElse, hl fuel (Nat.le_trans (Nat.le_max_left _ _) hfuel)]
  exact hr fuel (Nat.le_trans (Nat.le_max_right _ _) hfuel)

/-- info: 'P4SpecTec.Refine.EventuallyRuns.orElseUnmatch'
depends on axioms: [propext] -/
#guard_msgs in #print axioms EventuallyRuns.orElseUnmatch

/-- Negation flips success and mismatch and preserves a hard error. -/
theorem EventuallyRuns.notHold {m : Nat → Eval α} (h : EventuallyRuns m r) :
    EventuallyRuns (fun fuel => Eval.notHold (m fuel))
      (match r with
       | .ok _ => .error .unmatch
       | .error .unmatch => .ok ()
       | .error .err => .error .err) := by
  obtain ⟨bound, hbound⟩ := h
  refine ⟨bound, fun fuel hfuel => ?_⟩
  rw [run_notHold, hbound fuel hfuel]
  cases r with
  | ok _ => rfl
  | error e => cases e <;> rfl

/-- info: 'P4SpecTec.Refine.EventuallyRuns.notHold'
does not depend on any axioms -/
#guard_msgs in #print axioms EventuallyRuns.notHold

/-- Eventual realization entails the design's existential reverse correspondence. -/
theorem Realizes.witness {P : α → β → Prop} {reference : Nat → Eval α}
    {generated : Eval β} (h : Realizes P reference generated)
    (hq : generated.run = some q) :
    ∃ fuel r, (reference fuel).run = some r ∧ ResRel P r q := by
  obtain ⟨r, hr, hrel⟩ := h q hq
  obtain ⟨fuel, hfuel⟩ := hr.witness
  exact ⟨fuel, r, hfuel, hrel⟩

/-- info: 'P4SpecTec.Refine.Realizes.witness'
depends on axioms: [propext] -/
#guard_msgs in #print axioms Realizes.witness

/-- Related pure values have a constant realization. -/
theorem Realizes.pure {P : α → β → Prop} (h : P a b) :
    Realizes P (fun _ => pure a) (pure b) := by
  intro q hq
  cases hq
  exact ⟨.ok a, EventuallyRuns.constant rfl, h⟩

/-- info: 'P4SpecTec.Refine.Realizes.pure'
depends on axioms: [propext] -/
#guard_msgs in #print axioms Realizes.pure

/-- Both failure kinds have constant realizations, independently of the value relation. -/
theorem Realizes.error (P : α → β → Prop) (e : Fail) :
    Realizes P (fun _ => throw e) (throw e) := by
  intro q hq
  cases hq
  exact ⟨.error e, EventuallyRuns.constant rfl, rfl⟩

/-- info: 'P4SpecTec.Refine.Realizes.error'
depends on axioms: [propext] -/
#guard_msgs in #print axioms Realizes.error

/-- Defined generated binds compose using the actual related intermediate values. -/
theorem Realizes.bind {P : α → β → Prop} {Q : γ → δ → Prop}
    {m : Nat → Eval α} {n : Eval β} {next : Nat → α → Eval γ} {cont : β → Eval δ}
    (hm : Realizes P m n)
    (hn : ∀ a b, P a b → Realizes Q (fun fuel => next fuel a) (cont b)) :
    Realizes Q (fun fuel => m fuel >>= next fuel) (n >>= cont) := by
  intro q hq
  rw [run_bind] at hq
  cases he : n.run with
  | none => simp [he] at hq
  | some s =>
    obtain ⟨r, hr, hrel⟩ := hm s he
    cases s with
    | error e =>
      simp only [he, Option.bind_some] at hq
      cases hq
      cases r with
      | ok a => cases hrel
      | error f =>
        cases hrel
        exact ⟨.error e, hr.bindError next, rfl⟩
    | ok b =>
      simp only [he, Option.bind_some] at hq
      cases r with
      | error e => cases hrel
      | ok a =>
        obtain ⟨out, hout, hresult⟩ := hn a b hrel q hq
        exact ⟨out, hr.bindOk hout, hresult⟩

/-- info: 'P4SpecTec.Refine.Realizes.bind'
depends on axioms: [propext] -/
#guard_msgs in #print axioms Realizes.bind

/-- Ordered generated alternatives compose only through matching failure kinds. -/
theorem Realizes.orElse {P : α → β → Prop} {m₁ m₂ : Nat → Eval α} {n₁ n₂ : Eval β}
    (h₁ : Realizes P m₁ n₁) (h₂ : Realizes P m₂ n₂) :
    Realizes P (fun fuel => Eval.orElse (m₁ fuel) (m₂ fuel)) (Eval.orElse n₁ n₂) := by
  intro q hq
  rw [run_orElse] at hq
  cases he : n₁.run with
  | none => simp [he] at hq
  | some s =>
    obtain ⟨r, hr, hrel⟩ := h₁ s he
    cases s with
    | ok b =>
      simp only [he, Option.bind_some] at hq
      cases hq
      cases r with
      | error e => cases hrel
      | ok a => exact ⟨.ok a, hr.orElseOk m₂, hrel⟩
    | error e =>
      cases r with
      | ok a => cases hrel
      | error f =>
        cases hrel
        cases e with
        | err =>
          simp only [he, Option.bind_some] at hq
          cases hq
          exact ⟨.error .err, hr.orElseError m₂, rfl⟩
        | unmatch =>
          simp only [he, Option.bind_some] at hq
          obtain ⟨out, hout, hresult⟩ := h₂ q hq
          exact ⟨out, hr.orElseUnmatch hout, hresult⟩

/-- info: 'P4SpecTec.Refine.Realizes.orElse'
depends on axioms: [propext] -/
#guard_msgs in #print axioms Realizes.orElse

/-- Ordered list traversal composes all outcomes, including a failing prefix.
Each finite traversal obtains a common reference bound through the bind rules. -/
theorem Realizes.mapM {P : α → β → Prop} {Q : γ → δ → Prop}
    {f : Nat → α → Eval γ} {g : β → Eval δ} {xs : List α} {ys : List β}
    (hinputs : List.Forall₂ P xs ys)
    (hsteps : ∀ a b, P a b → Realizes Q (fun fuel => f fuel a) (g b)) :
    Realizes (List.Forall₂ Q) (fun fuel => xs.mapM (f fuel)) (ys.mapM g) := by
  induction hinputs with
  | nil =>
    simp only [List.mapM_nil]
    exact Realizes.pure .nil
  | @cons a b xs ys hab _ ih =>
    simp only [List.mapM_cons]
    apply Realizes.bind (hsteps a b hab)
    intro c d hcd
    apply Realizes.bind ih
    intro cs ds htail
    exact Realizes.pure (.cons hcd htail)

/-- info: 'P4SpecTec.Refine.Realizes.mapM'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Realizes.mapM

/-- Negation preserves reverse realization, including both failure kinds. -/
theorem Realizes.notHold {P : α → β → Prop} {m : Nat → Eval α} {n : Eval β}
    (h : Realizes P m n) :
    Realizes (fun _ _ => True) (fun fuel => Eval.notHold (m fuel)) (Eval.notHold n) := by
  intro q hq
  rw [run_notHold] at hq
  cases hn : n.run with
  | none => simp [hn] at hq
  | some s =>
    obtain ⟨r, hr, hrel⟩ := h s hn
    cases s with
    | ok b =>
      simp only [hn, Option.bind_some] at hq
      cases hq
      cases r with
      | error _ => cases hrel
      | ok a => exact ⟨.error .unmatch, hr.notHold, rfl⟩
    | error e =>
      cases r with
      | ok _ => cases hrel
      | error f =>
        cases hrel
        cases e <;> simp only [hn, Option.bind_some] at hq <;> cases hq
        · exact ⟨.error .err, hr.notHold, rfl⟩
        · exact ⟨.ok (), hr.notHold, trivial⟩

/-- info: 'P4SpecTec.Refine.Realizes.notHold'
depends on axioms: [propext] -/
#guard_msgs in #print axioms Realizes.notHold

/-- Optional traversal evaluates exactly the present value and preserves its failures. -/
theorem Realizes.optionMapM {P : α → β → Prop} {Q : γ → δ → Prop}
    {f : Nat → α → Eval γ} {g : β → Eval δ} {x : Option α} {y : Option β}
    (hinputs : Option.Rel P x y)
    (hstep : ∀ a b, P a b → Realizes Q (fun fuel => f fuel a) (g b)) :
    Realizes (Option.Rel Q) (fun fuel => x.mapM (f fuel)) (y.mapM g) := by
  cases hinputs with
  | none => exact Realizes.pure .none
  | some hab =>
    simp only [Option.mapM_some, map_eq_pure_bind]
    apply Realizes.bind (hstep _ _ hab)
    intro c d hcd
    exact Realizes.pure (.some hcd)

/-- info: 'P4SpecTec.Refine.Realizes.optionMapM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Realizes.optionMapM

end P4SpecTec.Refine
