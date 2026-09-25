import P4SpecTec.Refine.Calc
import P4SpecTec.Prelude.StateEval

/-!
State-sensitive refinement foundation, not yet used by the interpreter or
generator. Every terminating result, including either failure, must match
at exactly the same post-state. The existing `ResRel` keeps failure kinds
distinct. Divergence remains the existing one-way partial-correctness boundary.

`RejectedPrefix` records failed ordered attempts without erasing their
effects. `MapSteps` records an ordered state chain, not independent pointwise
results. These witnesses are building blocks, not full AL derivation judgments.
-/

namespace P4SpecTec.Refine

open P4SpecTec.Prelude

/-- Simulation from identical initial states, with identical final states
for all terminating outcomes, including failures. -/
def StateRefines (P : α → β → Prop) (m : StateEval α) (n : StateEval β) : Prop :=
  ∀ s r t, StateEval.run m s = some (r, t) →
    ∃ r', StateEval.run n s = some (r', t) ∧ ResRel P r r'

/-- An interpreter-only step may be skipped only if each terminating
execution succeeds with the stated property and leaves state unchanged. -/
def StateEvals (m : StateEval α) (P : α → Prop) : Prop :=
  ∀ s r t, StateEval.run m s = some (r, t) → ∃ a, r = .ok a ∧ t = s ∧ P a

/-- Identity simulation preserves the value and both failure kinds. -/
theorem stateRefinesRefl (m : StateEval α) : StateRefines Eq m m := by
  intro s r t h
  exact ⟨r, h, by cases r <;> rfl⟩

/-- info: 'P4SpecTec.Refine.stateRefinesRefl' depends on axioms: [propext] -/
#guard_msgs in #print axioms stateRefinesRefl

/-- Related pure values refine each other without consuming state. -/
theorem stateRefinesPure {P : α → β → Prop} {a : α} {b : β} (h : P a b) :
    StateRefines P (pure a) (pure b) := by
  intro s r t hr
  cases hr
  exact ⟨.ok b, rfl, h⟩

/-- info: 'P4SpecTec.Refine.stateRefinesPure' depends on axioms: [propext] -/
#guard_msgs in #print axioms stateRefinesPure

/-- The same failure refines itself, preserving the current state. -/
theorem stateRefinesThrow (P : α → β → Prop) (e : Fail) :
    StateRefines P (throw e) (throw e) := by
  intro s r t hr
  cases hr
  exact ⟨.error e, rfl, rfl⟩

/-- info: 'P4SpecTec.Refine.stateRefinesThrow' depends on axioms: [propext] -/
#guard_msgs in #print axioms stateRefinesThrow

/-- Existing pure refinement lifts to exact state-sensitive refinement. -/
theorem stateRefinesLift {P : α → β → Prop} {m : Eval α} {n : Eval β}
    (h : Refines P m n) : StateRefines P (StateEval.liftEval m) (StateEval.liftEval n) := by
  intro s r t hr
  rw [StateEval.run_liftEval] at hr
  cases hm : m.run with
  | none => simp [hm] at hr
  | some v =>
    simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl⟩
    obtain ⟨v', hn, hp⟩ := h v hm
    exact ⟨v', by rw [StateEval.run_liftEval, hn]; rfl, hp⟩

/-- info: 'P4SpecTec.Refine.stateRefinesLift' depends on axioms: [propext] -/
#guard_msgs in #print axioms stateRefinesLift

/-- Bind composes simulations at the first computation's exact post-state. -/
theorem stateRefinesBind {P : α → β → Prop} {Q : γ → δ → Prop}
    {m : StateEval α} {n : StateEval β} {k : α → StateEval γ} {l : β → StateEval δ}
    (h₁ : StateRefines P m n) (h₂ : ∀ a b, P a b → StateRefines Q (k a) (l b)) :
    StateRefines Q (m >>= k) (n >>= l) := by
  intro s r t hr
  rw [StateEval.runBind] at hr
  cases hm : StateEval.run m s with
  | none => simp [hm] at hr
  | some v =>
    rcases v with ⟨v, u⟩
    obtain ⟨v', hn, hp⟩ := h₁ s v u hm
    cases v with
    | error e =>
      cases v' with
      | ok b => cases hp
      | error e' =>
        cases hp
        simp only [hm, Option.bind_some] at hr
        cases hr
        exact ⟨.error e, by rw [StateEval.runBind, hn]; rfl, rfl⟩
    | ok a =>
      cases v' with
      | error e => cases hp
      | ok b =>
        simp only [hm, Option.bind_some] at hr
        obtain ⟨r', hl, hq⟩ := h₂ a b hp u r t hr
        exact ⟨r', by rw [StateEval.runBind, hn]; exact hl, hq⟩

/-- info: 'P4SpecTec.Refine.stateRefinesBind' depends on axioms: [propext] -/
#guard_msgs in #print axioms stateRefinesBind

/-- Ordered alternatives simulate at the mismatching branch's post-state. -/
theorem stateRefinesOrElse {P : α → β → Prop}
    {m₁ m₂ : StateEval α} {n₁ n₂ : StateEval β}
    (h₁ : StateRefines P m₁ n₁) (h₂ : StateRefines P m₂ n₂) :
    StateRefines P (StateEval.orElse m₁ m₂) (StateEval.orElse n₁ n₂) := by
  intro s r t hr
  rw [StateEval.run_orElse] at hr
  cases hm : StateEval.run m₁ s with
  | none => simp [hm] at hr
  | some v =>
    rcases v with ⟨v, u⟩
    obtain ⟨v', hn, hp⟩ := h₁ s v u hm
    cases v with
    | ok a =>
      cases v' with
      | error e => cases hp
      | ok b =>
        simp only [hm] at hr
        cases hr
        exact ⟨.ok b, by rw [StateEval.run_orElse, hn]; rfl, hp⟩
    | error e =>
      cases v' with
      | ok b => cases hp
      | error e' =>
        cases hp
        cases e with
        | err =>
          simp only [hm] at hr
          cases hr
          exact ⟨.error .err, by rw [StateEval.run_orElse, hn]; rfl, rfl⟩
        | unmatch =>
          simp only [hm] at hr
          obtain ⟨r', hn', hp'⟩ := h₂ u r t hr
          exact ⟨r', by rw [StateEval.run_orElse, hn]; exact hn', hp'⟩

/-- info: 'P4SpecTec.Refine.stateRefinesOrElse' depends on axioms: [propext] -/
#guard_msgs in #print axioms stateRefinesOrElse

/-- Negation preserves simulation, including state consumed by failure. -/
theorem stateRefinesNotHold {P : α → β → Prop} {m : StateEval α} {n : StateEval β}
    (h : StateRefines P m n) :
    StateRefines (fun _ _ => True) (StateEval.notHold m) (StateEval.notHold n) := by
  intro s r t hr
  rw [StateEval.run_notHold] at hr
  cases hm : StateEval.run m s with
  | none => simp [hm] at hr
  | some v =>
    rcases v with ⟨v, u⟩
    obtain ⟨v', hn, hp⟩ := h s v u hm
    cases v with
    | ok a =>
      cases v' with
      | error e => cases hp
      | ok b =>
        simp only [hm] at hr
        cases hr
        exact ⟨.error .unmatch, by rw [StateEval.run_notHold, hn]; rfl, rfl⟩
    | error e =>
      cases v' with
      | ok b => cases hp
      | error e' =>
        cases hp
        cases e <;> simp only [hm] at hr <;> cases hr
        · exact ⟨.error .err, by rw [StateEval.run_notHold, hn]; rfl, rfl⟩
        · exact ⟨.ok (), by rw [StateEval.run_notHold, hn]; rfl, trivial⟩

/-- info: 'P4SpecTec.Refine.stateRefinesNotHold' depends on axioms: [propext] -/
#guard_msgs in #print axioms stateRefinesNotHold

/-- A pure interpreter step satisfying `Evals` is safe to skip after lifting. -/
theorem stateEvalsLift {m : Eval α} {P : α → Prop} (h : Evals m P) :
    StateEvals (StateEval.liftEval m) P := by
  intro s r t hr
  rw [StateEval.run_liftEval] at hr
  cases hm : m.run with
  | none => simp [hm] at hr
  | some v =>
    simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl⟩
    obtain ⟨a, ha, hp⟩ := h v hm
    exact ⟨a, ha, rfl, hp⟩

/-- info: 'P4SpecTec.Refine.stateEvalsLift' depends on axioms: [propext] -/
#guard_msgs in #print axioms stateEvalsLift

/-- Skipping an interpreter-only step requires both success and no state change. -/
theorem stateRefinesBindEvals {P : α → Prop} {Q : γ → δ → Prop}
    {m : StateEval α} {k : α → StateEval γ} {n : StateEval δ}
    (h₁ : StateEvals m P) (h₂ : ∀ a, P a → StateRefines Q (k a) n) :
    StateRefines Q (m >>= k) n := by
  intro s r t hr
  rw [StateEval.runBind] at hr
  cases hm : StateEval.run m s with
  | none => simp [hm] at hr
  | some v =>
    rcases v with ⟨v, u⟩
    obtain ⟨a, rfl, rfl, hp⟩ := h₁ s v u hm
    simp only [hm, Option.bind_some] at hr
    exact h₂ a hp u r t hr

/-- info: 'P4SpecTec.Refine.stateRefinesBindEvals' depends on axioms: [propext] -/
#guard_msgs in #print axioms stateRefinesBindEvals

/-- Finite evidence of an ordered prefix of complete mismatching attempts.
Errors and successes cannot be skipped; every consumed state is retained. -/
inductive RejectedPrefix : List (StateEval α) → FreshState → FreshState → Prop where
  /-- An empty prefix consumes no state. -/
  | nil (s) : RejectedPrefix [] s s
  /-- Retry only after a mismatch, at that attempt's post-state. -/
  | cons {a as s t u} : StateEval.run a s = some (.error .unmatch, t) →
      RejectedPrefix as t u → RejectedPrefix (a :: as) s u

/-- Try a finite list of attempts in order, then a supplied fallback. -/
def tryPrefix (as : List (StateEval α)) (fallback : StateEval α) : StateEval α :=
  as.foldr StateEval.orElse fallback

/-- A rejected prefix resumes the fallback at its exact final state. -/
theorem rejectedPrefixRun {as : List (StateEval α)} {s t : FreshState}
    (h : RejectedPrefix as s t) (fallback : StateEval α) :
    StateEval.run (tryPrefix as fallback) s = StateEval.run fallback t := by
  induction h with
  | nil => rfl
  | cons ha _ ih =>
    change StateEval.run (StateEval.orElse _ _) _ = _
    rw [StateEval.run_orElse_unmatch _ _ _ _ ha]
    exact ih

/-- info: 'P4SpecTec.Refine.rejectedPrefixRun' does not depend on any axioms -/
#guard_msgs in #print axioms rejectedPrefixRun

/-- Successful ordered iteration, with one linked state transition per element. -/
inductive MapSteps (f : α → StateEval β) :
    List α → FreshState → List β → FreshState → Prop where
  /-- The empty iteration preserves state. -/
  | nil (s) : MapSteps f [] s [] s
  /-- An element runs before the remaining elements, using its post-state. -/
  | cons {a as s b t bs u} : StateEval.run (f a) s = some (.ok b, t) →
      MapSteps f as t bs u → MapSteps f (a :: as) s (b :: bs) u

/-- An ordered state chain executes to its recorded list and final state. -/
theorem mapStepsRun {f : α → StateEval β} {as : List α} {bs : List β}
    {s t : FreshState} (h : MapSteps f as s bs t) :
    StateEval.run (as.mapM f) s = some (.ok bs, t) := by
  induction h with
  | nil => rfl
  | cons ha _ ih =>
    rw [List.mapM_cons, StateEval.runBind, ha]
    change StateEval.run (do let bs ← _; pure (_ :: bs)) _ = _
    rw [StateEval.runBind, ih]
    rfl

/-- info: 'P4SpecTec.Refine.mapStepsRun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mapStepsRun

/-- Every successful iteration supplies an ordered chain of state witnesses. -/
theorem runMapMSteps {f : α → StateEval β} {as : List α} {bs : List β}
    {s t : FreshState} (h : StateEval.run (as.mapM f) s = some (.ok bs, t)) :
    MapSteps f as s bs t := by
  induction as generalizing s bs with
  | nil => cases h; exact .nil _
  | cons a as ih =>
    rw [List.mapM_cons] at h
    obtain ⟨b, u, hb, hrest⟩ := (StateEval.runBindOk _ _ _ _ _).mp h
    obtain ⟨bs', v, hbs, hpure⟩ := (StateEval.runBindOk _ _ _ _ _).mp hrest
    simp only [StateEval.runPure, Option.some.injEq, Prod.mk.injEq,
      Except.ok.injEq] at hpure
    rcases hpure with ⟨rfl, rfl⟩
    exact .cons hb (ih hbs)

/-- info: 'P4SpecTec.Refine.runMapMSteps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms runMapMSteps

/-- Lists of related results, with equal length and corresponding order. -/
inductive ListResults (P : α → β → Prop) : List α → List β → Prop where
  /-- Empty result lists correspond. -/
  | nil : ListResults P [] []
  /-- Related heads precede related tails. -/
  | cons {a b as bs} : P a b → ListResults P as bs → ListResults P (a :: as) (b :: bs)

/-- Pointwise simulations compose in list order, retaining failure state too. -/
theorem stateRefinesMapM {P : β → γ → Prop} {f : α → StateEval β} {g : α → StateEval γ}
    (h : ∀ a, StateRefines P (f a) (g a)) (as : List α) :
    StateRefines (ListResults P) (as.mapM f) (as.mapM g) := by
  induction as with
  | nil => exact stateRefinesPure .nil
  | cons a as ih =>
    rw [List.mapM_cons, List.mapM_cons]
    apply stateRefinesBind (h a)
    intro b c hbc
    apply stateRefinesBind ih
    intro bs cs hbs
    exact stateRefinesPure (.cons hbc hbs)

/-- info: 'P4SpecTec.Refine.stateRefinesMapM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stateRefinesMapM

end P4SpecTec.Refine
