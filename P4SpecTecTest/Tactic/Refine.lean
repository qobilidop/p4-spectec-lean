import P4SpecTec.Tactic.Refine.Normalize

/-! Regression checks for prepared refinement simplifier rules and fresh local facts. -/

open Lean Elab Tactic P4SpecTec.Tactic

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
/-- info: Try this: simp only [Nat.zero_add] at h -/
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
