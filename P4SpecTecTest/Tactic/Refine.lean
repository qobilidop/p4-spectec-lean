import P4SpecTec.Tactic.Constants
import P4SpecTec.Tactic.Refine.Normalize

/-! Regression checks for prepared refinement simplifier rules and fresh local facts. -/

open Lean Elab Tactic P4SpecTec.Tactic

private abbrev EqnAlias (x : Nat) : Prop := ∀ n : Nat, x = Nat.succ n → False

-- Fact lookup keeps caller order and duplicates, and agrees with the direct lookup
-- on empty and singleton inputs.
set_option linter.unusedVariables false in
example (first : (0 : Nat) = 0) (second : (1 : Nat) = 1) : True := by
  run_tac
    unless (← factTypes []).isEmpty do throwError "empty fact lookup was not empty"
    let one ← factTypes [`first]
    let two ← factTypes [`second]
    unless one.size == 1 && two.size == 1 do
      throwError "singleton fact lookup had the wrong size"
    unless (← factTypes [`second, `first, `second]) == #[two[0]!, one[0]!, two[0]!] do
      throwError "multi-fact lookup changed order or duplicates"
    let missing ← try
      let _ ← factTypes [`missing]
      pure false
    catch _ => pure true
    unless missing do throwError "missing fact lookup succeeded"
    evalTactic (← `(tactic| have $(mkIdent `first):ident : (2 : Nat) = 2 := rfl))
    let expected ← withMainContext do
      let some latest := (← getLCtx).findFromUserName? `first
        | throwError "shadowed fact was missing"
      instantiateMVars latest.type
    unless (← factTypes [`first]) == #[expected] &&
        (← factTypes [`first, `second])[0]! == expected do
      throwError "fact lookup did not select the latest shadowed user name"
  trivial

-- Direct inductive propositions cannot match the default discharger's forall-shaped
-- equation hypothesis, while an aliased forall can. Explicit rewrite facts remain keyed.
set_option linter.unusedVariables false in
example (p q : Prop) (hEq : (0 : Nat) = 0) (hHEq : HEq (0 : Nat) (0 : Nat))
    (hAnd : p ∧ q) (hOr : p ∨ q) (hTrue : True) (hFalse : False)
    (hAlias : EqnAlias 0) : True := by
  run_tac
    let ctx ← getLCtx
    let typeOf (name : Name) : TacticM Expr := do
      let some decl := ctx.findFromUserName? name | throwError "missing {name}"
      pure ((← instantiateMVars decl.type).consumeMData)
    let assumptions ← dischargeAssumptions
    for name in [`hEq, `hHEq, `hAnd, `hOr, `hTrue, `hFalse] do
      if assumptions.contains (← typeOf name) then
        throwError "rigid proposition {name} remained in discharge assumptions"
    unless assumptions.contains (← typeOf `hAlias) do
      throwError "reducible forall alias was omitted from discharge assumptions"
    unless (← closedInputs [`hEq]).contains (← typeOf `hEq) do
      throwError "explicit equality rewrite fact was omitted from closed inputs"
  trivial

-- A selected open equality can discharge a selected conditional rewrite of a closed
-- imported term. The first failed simplification must not be reused after it arrives.
set_option linter.unusedVariables false in
example (n : Nat)
    (rf_c_cond : n = 0 → Classical.choice (show Nonempty Nat from ⟨0⟩) = 0) : True := by
  run_tac
    let s ← prepareSimpSet { lemmas := #[], procs := #[] }
    let saved ← saveState
    let marker ← instantiateMVars (← Term.elabTerm
      (← `(term| Classical.choice (show Nonempty Nat from ⟨0⟩))) none)
    let target ← instantiateMVars (← Term.elabTerm
      (← `(term| Classical.choice (show Nonempty Nat from ⟨0⟩) = 0)) none)
    let scratch ← Meta.mkFreshExprSyntheticOpaqueMVar target
    setGoals [scratch.mvarId!]
    if ← normalize s then
      throwError "conditional rewrite applied before its side condition was known"
    let before ← closedInputs (← factHyps)
    let some prepared := s.prepared? | throwError "prepared simp state is missing"
    unless ((← prepared.closed.get).getD before {}).contains marker do
      throwError "closed marker was not cached before the new equality"
    evalTactic (← `(tactic| by_cases $(mkIdent `rf_c_eq):ident :
      $(mkIdent `n):ident = 0))
    let positive := (← getGoals).head!
    setGoals [positive]
    unless before != (← closedInputs (← factHyps)) do
      throwError "selected open equality did not partition the closed cache"
    unless ← normalize s do
      throwError "conditional closed rewrite missed the newly selected equality"
    unless (← getGoals).isEmpty do
      throwError "conditional closed rewrite did not close the positive branch"
    saved.restore
  trivial

-- An unused rigid equality does not partition either cache. Selecting it for rewriting does.
set_option linter.unusedVariables false in
example (unusedEq : (0 : Nat) = 0) : True := by
  run_tac
    let s ← prepareSimpSet { lemmas := #[], procs := #[] }
    let keyBefore ← normalizationKey s [] none
    let closedBefore ← closedInputs []
    unless closedBefore != (← closedInputs [`unusedEq]) do
      throwError "selected equality fact did not change the closed-input key"
    evalTactic (← `(tactic| clear $(mkIdent `unusedEq):ident))
    unless keyBefore == (← normalizationKey s [] none) &&
        closedBefore == (← closedInputs []) do
      throwError "unused rigid equality changed the discharge-only key"
  trivial

-- An aliased condition is available to simp's definitional-equality discharger. Both
-- no-progress and closed-result keys must change when it enters the local context.
example : True := by
  run_tac
    let s ← prepareSimpSet { lemmas := #[], procs := #[] }
    let before ← normalizationKey s [] none
    let closedBefore ← closedInputs []
    evalTactic (← `(tactic| have hidden : EqnAlias 0 := by intro n h; cases h))
    let after ← normalizationKey s [] none
    let closedAfter ← closedInputs []
    unless before != after && closedBefore != closedAfter do
      throwError "aliased discharge condition was missing from the cache keys"
  trivial

-- A prefix scanned in two different imported environments must use each environment's
-- module data, even within the same process.
example : True := by
  run_tac
    let env ← getEnv
    let empty ← mkEmptyEnvironment
    setEnv empty
    let fromEmpty ← importedUnder `P4SpecTec.Tactic
    setEnv env
    let fromImports ← importedUnder `P4SpecTec.Tactic
    unless fromEmpty.isEmpty && !fromImports.isEmpty do
      throwError "imported constants were reused across environments"
  trivial

-- A caller extending the rule names must not reuse the original empty preparation.
example (n : Nat) : 0 + n = n := by
  run_tac
    let s ← prepareSimpSet { lemmas := #[], procs := #[] }
    let s := { s with lemmas := #[``Nat.zero_add] }
    unless ← normalize s do throwError "extended rules were not applied"

-- One prepared global context can serve sibling goals with opposing local facts.
example (p : Prop) [Decidable p] : if p then p else ¬p := by
  run_tac
    let s ← prepareSimpSet { lemmas := #[``not_false_eq_true], procs := #[``reduceIte] }
    evalTactic (← `(tactic| by_cases $(mkIdent `rf_c):ident : $(mkIdent `p):ident))
    let goals ← getGoals
    for goal in goals do
      setGoals [goal]
      unless ← normalize s do throwError "current branch fact was not applied"
      unless (← getGoals).isEmpty do throwError "branch was not closed"

-- A hypothesis cannot discharge itself when normalizing its own statement.
example (p : Prop) (rf_c : p) : p := by
  run_tac
    let s ← prepareSimpSet { lemmas := #[], procs := #[] }
    if ← normalizeAt s `rf_c then throwError "hypothesis used itself"
  exact rf_c

-- Preparation rejects local rules instead of retaining them across goal contexts.
example (p : Prop) (rf_c : p) : p := by
  run_tac
    let rejected ← try
      let _ ← withoutRecover (prepareSimpSet { lemmas := #[`rf_c], procs := #[] })
      pure false
    catch _ => pure true
    unless rejected do throwError "preparation retained a local fact"
  exact rf_c

-- Tracing identifies the hypothesis location and the fixed rule actually used.
/-- info: Try this: simp (maxSteps✝ := 1000000) only [Nat.zero_add] at h -/
#guard_msgs in
set_option tactic.simp.trace true in
example (n m : Nat) (h : 0 + n = m) : n = m := by
  run_tac
    let s ← prepareSimpSet { lemmas := #[``Nat.zero_add], procs := #[] }
    unless ← normalizeAt s `h do throwError "hypothesis was not normalized"
  exact h

-- No-progress failure restores the exact goal, leaving subsequent tactics usable.
example (p : Prop) (h : p) : p := by
  run_tac
    let s ← prepareSimpSet { lemmas := #[], procs := #[] }
    let before ← getGoals
    if ← normalize s then throwError "normalization unexpectedly changed the goal"
    unless before == (← getGoals) do throwError "no-progress failure changed the goals"
  exact h
-- Canonical observations of raw tuple projections remain usable after constructor assembly.
theorem canonicalProjectionFact (pair : Nat × P4SpecTec.Lang.Il.value)
    (value : P4SpecTec.Lang.Il.value)
    (h : P4SpecTec.Refine.canon pair.2 = P4SpecTec.Refine.canon value) :
    [P4SpecTec.Refine.canon pair.2] = [P4SpecTec.Refine.canon value] := by
  run_tac
    let _ ← normalize { lemmas := #[], procs := #[] }
    unless (← getGoals).isEmpty do throwError "canonical projection fact was not used"

/-- info: 'canonicalProjectionFact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms canonicalProjectionFact
