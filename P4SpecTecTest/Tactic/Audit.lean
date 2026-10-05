import P4SpecTec.Tactic.Audit

/-! The axiom audit: one command for several theorems, with the declarations of this
module visited once for all of them, rejects exactly what `#print axioms` reports. -/

namespace P4SpecTecTest.Audit

axiom assumed : 1 = 1

theorem clean : 2 = 2 := rfl
theorem classical (p : Prop) : p ∨ ¬p := Classical.em p
theorem viaAxiom : 1 = 1 := assumed
-- The axiom is reached through another declaration of this module.
theorem viaLemma : 1 = 1 ∧ 2 = 2 := ⟨viaAxiom, clean⟩
set_option warn.sorry false in
theorem unfinished : 3 = 3 := sorry

#audit_axioms clean
#audit_axioms clean classical

/-- error: P4SpecTecTest.Audit.viaAxiom depends on axioms outside the allowed set:
[P4SpecTecTest.Audit.assumed] -/
#guard_msgs (whitespace := lax) in #audit_axioms viaAxiom

/-- error: P4SpecTecTest.Audit.viaLemma depends on axioms outside the allowed set:
[P4SpecTecTest.Audit.assumed] -/
#guard_msgs (whitespace := lax) in #audit_axioms viaLemma

/-- error: P4SpecTecTest.Audit.unfinished depends on axioms outside the allowed set:
[sorryAx] -/
#guard_msgs (whitespace := lax) in #audit_axioms unfinished

-- One bad theorem among several fails the command, wherever it stands, and a declaration
-- already visited for an earlier name still counts for a later one.
/-- error: [P4SpecTecTest.Audit.clean, P4SpecTecTest.Audit.viaAxiom,
 P4SpecTecTest.Audit.viaLemma] depends on axioms outside the allowed set:
[P4SpecTecTest.Audit.assumed] -/
#guard_msgs (whitespace := lax) in #audit_axioms clean viaAxiom viaLemma

/-- error: [P4SpecTecTest.Audit.viaLemma, P4SpecTecTest.Audit.classical] depends on axioms
outside the allowed set: [P4SpecTecTest.Audit.assumed] -/
#guard_msgs (whitespace := lax) in #audit_axioms viaLemma classical

end P4SpecTecTest.Audit
