import P4SpecTec.Refine.Realize

/-! Exact ordered-choice equations for matching differently grouped source alternatives. -/

namespace P4SpecTec.Refine

open P4SpecTec.Prelude

/-- Reassociation preserves first success, hard error, and undefined evaluation. -/
theorem orElseAssoc {α : Type} (a b c : Eval α) :
    Eval.orElse (Eval.orElse a b) c = Eval.orElse a (Eval.orElse b c) := by
  cases a with
  | none => rfl
  | some result =>
    cases result with
    | ok value => rfl
    | error failure => cases failure <;> rfl

/-- info: 'P4SpecTec.Refine.orElseAssoc' does not depend on any axioms -/
#guard_msgs in #print axioms orElseAssoc

/-- A retryable mismatch selects the next alternative exactly. -/
theorem unmatchOrElse {α : Type} (next : Eval α) :
    Eval.orElse (throw Fail.unmatch) next = next := rfl

/-- info: 'P4SpecTec.Refine.unmatchOrElse' does not depend on any axioms -/
#guard_msgs in #print axioms unmatchOrElse

/-- A successful alternative prevents the following alternative from running. -/
theorem pureOrElse {α : Type} (value : α) (next : Eval α) :
    Eval.orElse (pure value) next = pure value := rfl

/-- info: 'P4SpecTec.Refine.pureOrElse' does not depend on any axioms -/
#guard_msgs in #print axioms pureOrElse

/-- A hard error prevents the following alternative from running. -/
theorem errorOrElse {α : Type} (next : Eval α) :
    Eval.orElse (throw Fail.err) next = throw Fail.err := rfl

/-- info: 'P4SpecTec.Refine.errorOrElse' does not depend on any axioms -/
#guard_msgs in #print axioms errorOrElse

end P4SpecTec.Refine
