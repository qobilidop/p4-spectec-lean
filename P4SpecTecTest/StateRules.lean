import P4SpecTec.Refine.StateCalc

/-!
Bounded positivity experiment for structural, ordered iteration of stateful
relation premises. No code generator or generic proof automation is enabled.
-/

namespace P4SpecTecTest.StateRules

open P4SpecTec.Prelude P4SpecTec.Refine

inductive StateChain (P : α → FreshState → β → FreshState → Prop) :
    List α → FreshState → List β → FreshState → Prop where
  | nil (s) : StateChain P [] s [] s
  | cons {a as s b t bs u} : P a s b t →
      StateChain P as t bs u → StateChain P (a :: as) s (b :: bs) u

theorem chainOfMapSteps {P : α → FreshState → β → FreshState → Prop}
    {f : α → StateEval β}
    (step : ∀ a s b t, StateEval.run (f a) s = some (.ok b, t) → P a s b t)
    {as : List α} {s : FreshState} {bs : List β} {t : FreshState}
    (h : MapSteps f as s bs t) : StateChain P as s bs t := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (step _ _ _ _ h) ih

/-- info: 'P4SpecTecTest.StateRules.chainOfMapSteps' does not depend on any axioms -/
#guard_msgs in #print axioms chainOfMapSteps

abbrev Program := Nat → FreshState → Option (Except Fail (List String) × FreshState)

abbrev rejected (f : Program) (n : Nat) : StateEval (List String) := do
  let _ ← StateEval.freshTypeId
  match n with
  | 0 => throw .unmatch
  | n + 1 =>
    let _ ← (ExceptT.mk (f n) : StateEval (List String))
    throw .unmatch

abbrev selected (f : Program) (n : Nat) : StateEval (List String) :=
  match n with
  | 0 => do
    let x ← StateEval.freshTypeId
    pure [x]
  | n + 1 => do
    let xss ← [n, n].mapM (fun k => (ExceptT.mk (f k) : StateEval (List String)))
    pure xss.flatten

def visits (n : Nat) (s : FreshState) : Option (Except Fail (List String) × FreshState) :=
  StateEval.run ((do
    let _ ← StateEval.freshTypeId
    match n with
    | 0 => throw .unmatch
    | n + 1 =>
      let _ ← (ExceptT.mk (visits n) : StateEval (List String))
      throw .unmatch) <|>
    (match n with
    | 0 => do
      let x ← StateEval.freshTypeId
      pure [x]
    | n + 1 => do
      let xss ← [n, n].mapM (fun k => (ExceptT.mk (visits k) : StateEval (List String)))
      pure xss.flatten)) s
partial_fixpoint

/-- info: 'P4SpecTecTest.StateRules.visits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms visits

inductive Visits : Nat → FreshState → List String → FreshState → Prop where
  | leaf {s u} : RejectedPrefix [rejected visits 0] s u →
      Visits 0 s ["FRESH__" ++ toString u.counter] u.next
  | node {n s u xss t} : RejectedPrefix [rejected visits (n + 1)] s u →
      StateChain Visits [n, n] u xss t → Visits (n + 1) s xss.flatten t

theorem transport {a b : StateEval α} (h : StateRefines Eq a b)
    {s : FreshState} {r : Except Fail α × FreshState}
    (hr : StateEval.run a s = some r) : StateEval.run b s = some r := by
  rcases r with ⟨r, t⟩
  obtain ⟨r', hb, he⟩ := h s r t hr
  have eq : r = r' := by cases r <;> cases r' <;> simp_all [ResRel]
  cases eq
  exact hb

/-- info: 'P4SpecTecTest.StateRules.transport' depends on axioms: [propext] -/
#guard_msgs in #print axioms transport

theorem realization {a b : FreshState → Option (Except Fail α × FreshState)}
    (h : ∀ s r, a s = some r → b s = some r) :
    StateRefines Eq (ExceptT.mk a) (ExceptT.mk b) := by
  intro s r t hr
  exact ⟨r, h s (r, t) hr, by cases r <;> rfl⟩

/-- info: 'P4SpecTecTest.StateRules.realization' depends on axioms: [propext] -/
#guard_msgs in #print axioms realization

theorem rejectedRef {f g : Program}
    (h : ∀ n, StateRefines Eq (ExceptT.mk (f n)) (ExceptT.mk (g n))) (n : Nat) :
    StateRefines Eq (rejected f n) (rejected g n) := by
  apply stateRefinesBind (stateRefinesRefl _)
  intro x y he
  cases he
  cases n with
  | zero => exact stateRefinesRefl _
  | succ n =>
    apply stateRefinesBind (h n)
    intro xs ys he
    cases he
    exact stateRefinesRefl _

/-- info: 'P4SpecTecTest.StateRules.rejectedRef' depends on axioms: [propext] -/
#guard_msgs in #print axioms rejectedRef

theorem listResultsEq {as bs : List α} (h : ListResults Eq as bs) : as = bs := by
  induction h with
  | nil => rfl
  | cons h _ ih => cases h; cases ih; rfl

/-- info: 'P4SpecTecTest.StateRules.listResultsEq' does not depend on any axioms -/
#guard_msgs in #print axioms listResultsEq

theorem selectedRef {f g : Program}
    (h : ∀ n, StateRefines Eq (ExceptT.mk (f n)) (ExceptT.mk (g n))) (n : Nat) :
    StateRefines Eq (selected f n) (selected g n) := by
  cases n with
  | zero => exact stateRefinesRefl _
  | succ n =>
    apply stateRefinesBind (stateRefinesMapM h [n, n])
    intro xs ys he
    cases listResultsEq he
    exact stateRefinesRefl _

/-- info: 'P4SpecTecTest.StateRules.selectedRef' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms selectedRef

theorem rejectedNotOk (f : Program) (n : Nat) (s : FreshState)
    (r : Except Fail (List String) × FreshState)
    (hr : StateEval.run (rejected f n) s = some r) : ∀ xs, r.1 ≠ .ok xs := by
  rw [StateEval.runBind, StateEval.run_freshTypeId] at hr
  simp only [Option.bind_some] at hr
  cases n with
  | zero => cases hr; intro xs he; cases he
  | succ n =>
    rw [StateEval.runBind] at hr
    cases hc : f n s.next with
    | none => simp [StateEval.run, hc] at hr
    | some result =>
      rcases result with ⟨result, u⟩
      cases result <;> simp [StateEval.run, hc] at hr <;>
        cases hr <;> intro xs he <;> cases he

/-- info: 'P4SpecTecTest.StateRules.rejectedNotOk' depends on axioms: [propext] -/
#guard_msgs in #print axioms rejectedNotOk

theorem visitsSound (n : Nat) (s : FreshState) (xs : List String) (t : FreshState)
    (h : visits n s = some (.ok xs, t)) : Visits n s xs t := by
  have all := visits.partial_correctness
    (motive := fun n s r => visits n s = some r ∧
      ∀ xs t, r = (.ok xs, t) → Visits n s xs t)
    (by
      intro rec ih n s r hr
      have hcall (k) := realization (fun s r h => (ih k s r h).1)
      have hrej := rejectedRef hcall n
      have hsel := selectedRef hcall n
      change StateEval.run (StateEval.orElse (rejected rec n) (selected rec n)) s = some r
        at hr
      constructor
      · rw [visits.eq_def]
        exact transport (stateRefinesOrElse hrej hsel) hr
      · intro xs t he
        cases he
        rw [StateEval.run_orElse] at hr
        cases hj : StateEval.run (rejected rec n) s with
        | none => simp [hj] at hr
        | some result =>
          rcases result with ⟨result, u⟩
          cases result with
          | ok v => exact False.elim (rejectedNotOk rec n s _ hj v rfl)
          | error e =>
            cases e with
            | err => simp [hj] at hr
            | unmatch =>
              simp only [hj] at hr
              change StateEval.run (selected rec n) u = some (.ok xs, t) at hr
              have hprefix : RejectedPrefix [rejected visits n] s u :=
                .cons (transport hrej hj) (.nil u)
              cases n with
              | zero =>
                obtain ⟨x, v, hx, hpure⟩ := (StateEval.runBindOk _ _ _ _ _).mp hr
                simp only [StateEval.run_freshTypeId, Option.some.injEq, Prod.mk.injEq,
                  Except.ok.injEq] at hx
                rcases hx with ⟨rfl, rfl⟩
                cases hpure
                exact .leaf hprefix
              | succ n =>
                obtain ⟨xss, v, hmap, hpure⟩ := (StateEval.runBindOk _ _ _ _ _).mp hr
                cases hpure
                apply Visits.node hprefix
                apply chainOfMapSteps (f := fun k => ExceptT.mk (rec k)) ?_
                  (runMapMSteps hmap)
                intro k s ys t hcall
                exact (ih k s (.ok ys, t) hcall).2 ys t rfl)
    n s (.ok xs, t) h
  exact all.2 xs t rfl

/-- info: 'P4SpecTecTest.StateRules.visitsSound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms visitsSound

local instance [BEq α] : BEq (Except Fail α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

#guard visits 0 0 == some (.ok ["FRESH__1"], FreshState.ofInt 2)
#guard visits 1 0 == some (.ok ["FRESH__4", "FRESH__6"], FreshState.ofInt 7)
#guard visits 2 0 ==
  some (.ok ["FRESH__12", "FRESH__14", "FRESH__19", "FRESH__21"], FreshState.ofInt 22)
#guard StateEval.run (rejected visits 2) 0 ==
  some (.error .unmatch, FreshState.ofInt 8)

/-- error: (kernel) invalid nested inductive datatype 'P4SpecTecTest.StateRules.StateChain',
nested inductive datatypes parameters cannot contain local variables. -/
#guard_msgs in
inductive Captured : Nat → FreshState → List String → FreshState → Prop where
  | node {n s xss t} :
      StateChain (fun (_ : Unit) u xs v => Captured n u xs v) [(), ()] s xss t →
      Captured (n + 1) s xss.flatten t

end P4SpecTecTest.StateRules
