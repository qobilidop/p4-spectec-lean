import P4SpecTec.Tactic.OutcomeInduction
import P4SpecTec.Tactic.Audit
import P4SpecTec.Prelude.Eval

/-! Joint outcome induction must match functions, even when conjunct order is reversed. -/

namespace P4SpecTecTest.Tactic.OutcomeInduction

open P4SpecTec P4SpecTec.Prelude Lean Elab Tactic

mutual
  def left (b : Bool) : Option (Except Fail Unit) :=
    if b then right false else some (.ok ())
  partial_fixpoint

  def right (b : Bool) : Option (Except Fail Unit) :=
    if b then left false else some (.ok ())
  partial_fixpoint
end

elab "prove_test_group" : tactic => do
  P4SpecTec.Tactic.proveOutcomeGroup ``left.mutual_partial_correctness do
    evalTactic (← `(tactic| intro rec ih b result run))
    evalTactic (← `(tactic| cases b))
    evalTactic (← `(tactic| all_goals simp only [Bool.false_eq_true, ite_false, ite_true] at run))
    evalTactic (← `(tactic| first | exact (Option.some.inj run).symm | exact ih false result run))
    evalTactic (← `(tactic| first | exact (Option.some.inj run).symm | exact ih false result run))

theorem reordered :
    (∀ b result, right b = some result → result = .ok ()) ∧
    (∀ b result, left b = some result → result = .ok ()) := by
  prove_test_group

/-- info: 'P4SpecTecTest.Tactic.OutcomeInduction.reordered' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reordered

end P4SpecTecTest.Tactic.OutcomeInduction
