import P4SpecTec.Refine.StateCalc

/-!
Bounded state-sensitive proof fixtures. The recursive relation has genuine
structural rules and explicit rejected-prefix witnesses; it is not defined
as an equation with its evaluator. No AL integration is claimed.
-/

namespace P4SpecTecTest.StateCalc

open P4SpecTec.Prelude P4SpecTec.Refine

def rejected : StateEval (List String) := do
  let _ ← StateEval.freshTypeId
  throw .unmatch

def ids (n : Nat) (s : FreshState) : Option (Except Fail (List String) × FreshState) :=
  StateEval.run (StateEval.orElse rejected (match n with
    | 0 => pure []
    | n + 1 => do
      let x ← StateEval.freshTypeId
      let xs ← (ExceptT.mk (ids n) : StateEval (List String))
      pure (x :: xs))) s
partial_fixpoint

/-- info: 'P4SpecTecTest.StateCalc.ids' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ids

inductive Ids : Nat → FreshState → List String → FreshState → Prop where
  | nil {s u} : RejectedPrefix [rejected] s u → Ids 0 s [] u
  | cons {n s u xs t} : RejectedPrefix [rejected] s u →
      Ids n u.next xs t → Ids (n + 1) s (("FRESH__" ++ toString u.counter) :: xs) t

theorem rejectedRun (s : FreshState) :
    StateEval.run rejected s = some (.error .unmatch, s.next) := by
  rw [rejected, StateEval.runBind, StateEval.run_freshTypeId]
  rfl

/-- info: 'P4SpecTecTest.StateCalc.rejectedRun' depends on axioms: [propext] -/
#guard_msgs in #print axioms rejectedRun

theorem idsSound (n : Nat) (s : FreshState) (xs : List String) (t : FreshState)
    (h : ids n s = some (.ok xs, t)) : Ids n s xs t := by
  have all := ids.partial_correctness
    (motive := fun n s r => ∀ xs t, r = (.ok xs, t) → Ids n s xs t)
    (by
      intro rec ih n s r hr xs t he
      cases he
      rw [StateEval.run_orElse_unmatch _ _ _ _ (rejectedRun s)] at hr
      have hprefix : RejectedPrefix [rejected] s s.next :=
        .cons (rejectedRun s) (.nil s.next)
      cases n with
      | zero => cases hr; exact .nil hprefix
      | succ n =>
        obtain ⟨x, u, hx, hrest⟩ := (StateEval.runBindOk _ _ _ _ _).mp hr
        simp only [StateEval.run_freshTypeId, Option.some.injEq, Prod.mk.injEq,
          Except.ok.injEq] at hx
        rcases hx with ⟨rfl, rfl⟩
        obtain ⟨ys, v, hy, hend⟩ := (StateEval.runBindOk _ _ _ _ _).mp hrest
        simp only [StateEval.runPure, Option.some.injEq, Prod.mk.injEq,
          Except.ok.injEq] at hend
        rcases hend with ⟨rfl, rfl⟩
        exact .cons hprefix (ih n s.next.next _ hy ys _ rfl))
    n s (.ok xs, t) h
  exact all xs t rfl

/-- info: 'P4SpecTecTest.StateCalc.idsSound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms idsSound

local instance [BEq α] : BEq (Except Fail α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

-- Each recursive level, including the base case, consumes a rejected attempt.
#guard ids 0 0 == some (.ok [], FreshState.ofInt 1)
#guard ids 2 0 == some (.ok ["FRESH__1", "FRESH__3"], FreshState.ofInt 5)
#guard ids 1 (FreshState.ofInt 4611686018427387902) ==
  some (.ok ["FRESH__4611686018427387903"], FreshState.ofInt (-4611686018427387903))

-- Equal failure tags are not enough when failed branches consume different state.
theorem failureStateMatters :
    ¬ StateRefines Eq rejected (throw .unmatch : StateEval (List String)) := by
  intro h
  obtain ⟨r, hr, _⟩ := h 0 (.error .unmatch) (FreshState.next 0) (rejectedRun 0)
  have bad : (0 : FreshState) = FreshState.next 0 :=
    congrArg Prod.snd (Option.some.inj hr)
  exact (by decide : (0 : FreshState) ≠ FreshState.next 0) bad

/-- info: 'P4SpecTecTest.StateCalc.failureStateMatters' depends on axioms: [propext] -/
#guard_msgs in #print axioms failureStateMatters

theorem failureKindMatters :
    ¬ StateRefines (fun (_ _ : Unit) => True) (throw .err) (throw .unmatch) := by
  intro h
  obtain ⟨r, hr, hp⟩ := h 0 (.error .err) 0 rfl
  cases hr
  cases hp

/-- info: 'P4SpecTecTest.StateCalc.failureKindMatters' depends on axioms: [propext] -/
#guard_msgs in #print axioms failureKindMatters

-- A computation that always succeeds is still unsafe to skip when it allocates.
theorem freshCannotSkip : ¬ StateEvals StateEval.freshTypeId (fun _ => True) := by
  intro h
  obtain ⟨_, _, hs, _⟩ := h 0 _ _ (StateEval.run_freshTypeId 0)
  exact (by decide : FreshState.next 0 ≠ (0 : FreshState)) hs

/-- info: 'P4SpecTecTest.StateCalc.freshCannotSkip' depends on axioms: [propext] -/
#guard_msgs in #print axioms freshCannotSkip

theorem orderedAllocations :
    MapSteps (fun (_ : Unit) => StateEval.freshTypeId) [(), ()] 0
      ["FRESH__0", "FRESH__1"] (FreshState.ofInt 2) := by
  apply runMapMSteps
  rfl

/-- info: 'P4SpecTecTest.StateCalc.orderedAllocations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms orderedAllocations

theorem twoRejectedAttempts :
    StateEval.run (tryPrefix [rejected, rejected] (pure [])) 0 =
      some (.ok [], FreshState.ofInt 2) := by
  have h : RejectedPrefix [rejected, rejected] 0 (FreshState.ofInt 2) :=
    .cons (rejectedRun 0) (.cons (rejectedRun (FreshState.next 0)) (.nil _))
  exact rejectedPrefixRun h (pure [])

/-- info: 'P4SpecTecTest.StateCalc.twoRejectedAttempts' depends on axioms: [propext] -/
#guard_msgs in #print axioms twoRejectedAttempts

-- Relation-changing bind and map rules are exercised, not only reflexivity.
theorem allocationLength :
    StateRefines (fun (s : String) (n : Nat) => s.length = n) StateEval.freshTypeId
      (do let s ← StateEval.freshTypeId; pure s.length) := by
  have h := stateRefinesBind (stateRefinesRefl StateEval.freshTypeId)
    (k := fun s => pure s) (l := fun s => pure s.length)
    (fun a b hab => by cases hab; exact stateRefinesPure rfl)
  simpa only [bind_pure] using h

/-- info: 'P4SpecTecTest.StateCalc.allocationLength' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocationLength

theorem allocationLengths :
    StateRefines (ListResults (fun (s : String) (n : Nat) => s.length = n))
      ([(), ()].mapM fun _ => StateEval.freshTypeId)
      ([(), ()].mapM fun _ => do let s ← StateEval.freshTypeId; pure s.length) :=
  stateRefinesMapM (fun _ => allocationLength) _

/-- info: 'P4SpecTecTest.StateCalc.allocationLengths' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocationLengths

end P4SpecTecTest.StateCalc
