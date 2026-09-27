import P4SpecTec.Tactic.CarrierInduction
import P4SpecTec.Tactic.Audit

/-! Actual native nested-recursion motive selection and fail-closed negative checks. -/

namespace P4SpecTecTest.Tactic.CarrierInduction

inductive Tree where
  | leaf : Tree
  | node : List Tree → Tree

mutual
  inductive Accepted : Tree → Prop where
    | leaf : Accepted .leaf
    | node (children : List Tree) : AcceptedList children → Accepted (.node children)
  inductive AcceptedList : List Tree → Prop where
    | nil : AcceptedList []
    | cons (head : Tree) (tail : List Tree) :
      Accepted head → AcceptedList tail → AcceptedList (head :: tail)
end

/-- Native nested induction uses exact predicates without a motive-order dependency. -/
theorem treeAccepted (tree : Tree) : Accepted tree := by
  carrier_induction Tree.rec [Accepted, AcceptedList]
  all_goals intros
  all_goals repeat first | assumption | constructor
/-- info: 'P4SpecTecTest.Tactic.CarrierInduction.treeAccepted' does not depend on any axioms -/
#guard_msgs in #print axioms treeAccepted
#audit_axioms treeAccepted

/-- error: ambiguous carrier predicate for recursor motive Tree → Prop -/
#guard_msgs in
example (tree : Tree) : Accepted tree := by
  carrier_induction Tree.rec [Accepted, fun (_ : Tree) => True, AcceptedList]

/-- error: no explicit carrier predicate for recursor motive List Tree → Prop -/
#guard_msgs in
example (tree : Tree) : Accepted tree := by
  carrier_induction Tree.rec [Accepted]

/-- error: carrier_induction requires a parameter-free native recursor -/
#guard_msgs in
example (items : List Nat) : True := by
  carrier_induction List.rec [fun (_ : List Nat) => True]

-- Explicit predicates and minor proofs may depend on the goal's local context.
example (p : Tree → Prop) (ps : List Tree → Prop)
    (leaf : p .leaf) (node : ∀ children, ps children → p (.node children))
    (nil : ps []) (cons : ∀ head tail, p head → ps tail → ps (head :: tail))
    (tree : Tree) : p tree := by
  carrier_induction Tree.rec [p, ps]
  all_goals assumption

/-- A mismatched conclusion fails without admitting or replacing the original goal. -/
theorem failedApplicationRetainsGoal : True := by
  fail_if_success carrier_induction Tree.rec [Accepted, AcceptedList]
  trivial
/-- info: 'P4SpecTecTest.Tactic.CarrierInduction.failedApplicationRetainsGoal'
does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms failedApplicationRetainsGoal
#audit_axioms failedApplicationRetainsGoal

/-- A failed predicate elaboration cannot recover by introducing an admitted proof. -/
theorem failedElaborationRetainsGoal : True := by
  fail_if_success carrier_induction Tree.rec [unknownPredicate, AcceptedList]
  trivial
/-- info: 'P4SpecTecTest.Tactic.CarrierInduction.failedElaborationRetainsGoal'
does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms failedElaborationRetainsGoal
#audit_axioms failedElaborationRetainsGoal

end P4SpecTecTest.Tactic.CarrierInduction
