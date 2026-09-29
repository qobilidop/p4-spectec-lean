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

/-- A shared prefix distributes over sequential choice. The prefix is deterministic, so both
alternatives see its same outcome; a mismatch in it fails both, as the second retry does.
This aligns generated rule groups (shared premises, then paths) with the reference's flat
sequence of rule paths, each repeating the group's premises. -/
theorem bindOrElse {α β : Type} (m : Eval α) (f g : α → Eval β) :
    (m >>= fun x => Eval.orElse (f x) (g x)) = Eval.orElse (m >>= f) (m >>= g) := by
  cases m with
  | none => rfl
  | some result =>
    cases result with
    | ok value => rfl
    | error failure => cases failure <;> rfl

/-- info: 'P4SpecTec.Refine.bindOrElse' does not depend on any axioms -/
#guard_msgs in #print axioms bindOrElse

/-- A shared local definition distributes over sequential choice. -/
theorem haveOrElse {α β : Type} (v : α) (f g : α → Eval β) :
    (have x := v; Eval.orElse (f x) (g x)) = Eval.orElse (have x := v; f x) (have x := v; g x) :=
  rfl

/-- info: 'P4SpecTec.Refine.haveOrElse' does not depend on any axioms -/
#guard_msgs in #print axioms haveOrElse

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
