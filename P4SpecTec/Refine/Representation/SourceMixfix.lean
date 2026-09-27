import P4SpecTec.Refine.Representation.Source

/-! Source notation matching and constructor-disjointness proof support.
This is our own proof support, not an upstream mirror. -/

namespace P4SpecTec.Refine.Representation.Source
open P4SpecTec.Domain
private theorem atomFork (a b c : Atom.t)
    (hab : Atom.eq a b = true) (hbc : Atom.eq a c = true) : Atom.eq b c = true := by
  have eqv : ∀ a b, Atom.eq a b = true ↔ a = b := by
    intro a b
    simp [Atom.eq, Atom.compare_eq_iff]
  exact (eqv b c).mpr (((eqv a b).mp hab).symm.trans ((eqv a c).mp hbc))
mutual
/-- Two source notations matching one tree match each other, regardless of field carriers. -/
theorem mixopFork {α β γ : Type} :
    ∀ (a : Mixfix.t α) (b : Mixfix.t β) (c : Mixfix.t γ),
      Mixfix.eq_mixop a b = true → Mixfix.eq_mixop a c = true →
        Mixfix.eq_mixop b c = true
  | a, b, c => by
    intro hab hbc
    rcases a with a | a | ⟨la, ma, ra⟩ | ⟨la, aa, ra⟩ | a <;>
    rcases b with b | b | ⟨lb, mb, rb⟩ | ⟨lb, ab, rb⟩ | b <;>
    rcases c with c | c | ⟨lc, mc, rc⟩ | ⟨lc, ac, rc⟩ | c <;>
      first
      | (simp only [Mixfix.eq_mixop, Mixfix.eq, Bool.false_eq_true] at hab hbc; done)
      | (rfl)
      | (exact atomFork a.it b.it c.it hab hbc)
      | (simp only [Mixfix.eq_mixop, Mixfix.eq, Bool.and_eq_true] at hab hbc ⊢
         exact ⟨⟨atomFork la.it lb.it lc.it hab.1.1 hbc.1.1,
           mixopFork ma mb mc hab.1.2 hbc.1.2⟩,
           atomFork ra.it rb.it rc.it hab.2 hbc.2⟩)
      | (simp only [Mixfix.eq_mixop, Mixfix.eq, Bool.and_eq_true] at hab hbc ⊢
         exact ⟨⟨atomFork aa.it ab.it ac.it hab.1.1 hbc.1.1,
           mixopFork la lb lc hab.1.2 hbc.1.2⟩,
           mixopFork ra rb rc hab.2 hbc.2⟩)
      | (simpa only [Mixfix.eq_mixop, Mixfix.eq] using mixopsFork a b c hab hbc)

/-- Two source sequences matching one sequence match each other. -/
theorem mixopsFork {α β γ : Type} :
    ∀ (a : List (Mixfix.t α)) (b : List (Mixfix.t β)) (c : List (Mixfix.t γ)),
      Mixfix.eq.eqs (fun _ _ => true) a b = true →
      Mixfix.eq.eqs (fun _ _ => true) a c = true →
        Mixfix.eq.eqs (fun _ _ => true) b c = true
  | [], [], [] => by intro _ _; rfl
  | [], [], _ :: _ => by simp [Mixfix.eq.eqs]
  | [], _ :: _, _ => by simp [Mixfix.eq.eqs]
  | _ :: _, [], _ => by simp [Mixfix.eq.eqs]
  | _ :: _, _ :: _, [] => by simp [Mixfix.eq.eqs]
  | a :: as, b :: bs, c :: cs => by
    intro hab hbc
    simp only [Mixfix.eq.eqs, Bool.and_eq_true] at hab hbc ⊢
    exact ⟨mixopFork a b c hab.1 hbc.1, mixopsFork as bs cs hab.2 hbc.2⟩
end
/-- info: 'P4SpecTec.Refine.Representation.Source.mixopFork' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixopFork
#audit_axioms mixopFork
/-- info: 'P4SpecTec.Refine.Representation.Source.mixopsFork' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixopsFork
#audit_axioms mixopsFork

private theorem atomTrans (a b c : Atom.t)
    (hab : Atom.eq a b = true) (hbc : Atom.eq b c = true) : Atom.eq a c = true := by
  have eqv : ∀ a b, Atom.eq a b = true ↔ a = b := by
    intro a b
    simp [Atom.eq, Atom.compare_eq_iff]
  exact (eqv a c).mpr ((eqv a b).mp hab |>.trans ((eqv b c).mp hbc))
mutual
/-- Source notation matching is transitive across different field-carrier types. -/
theorem mixopTrans {α β γ : Type} :
    ∀ (a : Mixfix.t α) (b : Mixfix.t β) (c : Mixfix.t γ),
      Mixfix.eq_mixop a b = true → Mixfix.eq_mixop b c = true →
        Mixfix.eq_mixop a c = true
  | a, b, c => by
    intro hab hbc
    rcases a with a | a | ⟨la, ma, ra⟩ | ⟨la, aa, ra⟩ | a <;>
    rcases b with b | b | ⟨lb, mb, rb⟩ | ⟨lb, ab, rb⟩ | b <;>
    rcases c with c | c | ⟨lc, mc, rc⟩ | ⟨lc, ac, rc⟩ | c <;>
      first
      | (simp only [Mixfix.eq_mixop, Mixfix.eq, Bool.false_eq_true] at hab hbc; done)
      | (rfl)
      | (exact atomTrans a.it b.it c.it hab hbc)
      | (simp only [Mixfix.eq_mixop, Mixfix.eq, Bool.and_eq_true] at hab hbc ⊢
         exact ⟨⟨atomTrans la.it lb.it lc.it hab.1.1 hbc.1.1,
           mixopTrans ma mb mc hab.1.2 hbc.1.2⟩,
           atomTrans ra.it rb.it rc.it hab.2 hbc.2⟩)
      | (simp only [Mixfix.eq_mixop, Mixfix.eq, Bool.and_eq_true] at hab hbc ⊢
         exact ⟨⟨atomTrans aa.it ab.it ac.it hab.1.1 hbc.1.1,
           mixopTrans la lb lc hab.1.2 hbc.1.2⟩,
           mixopTrans ra rb rc hab.2 hbc.2⟩)
      | (simpa only [Mixfix.eq_mixop, Mixfix.eq] using mixopsTrans a b c hab hbc)

/-- Source sequence notation matching is transitive. -/
theorem mixopsTrans {α β γ : Type} :
    ∀ (a : List (Mixfix.t α)) (b : List (Mixfix.t β)) (c : List (Mixfix.t γ)),
      Mixfix.eq.eqs (fun _ _ => true) a b = true →
      Mixfix.eq.eqs (fun _ _ => true) b c = true →
        Mixfix.eq.eqs (fun _ _ => true) a c = true
  | [], [], [] => by intro _ _; rfl
  | [], [], _ :: _ => by simp [Mixfix.eq.eqs]
  | [], _ :: _, _ => by simp [Mixfix.eq.eqs]
  | _ :: _, [], _ => by simp [Mixfix.eq.eqs]
  | _ :: _, _ :: _, [] => by simp [Mixfix.eq.eqs]
  | a :: as, b :: bs, c :: cs => by
    intro hab hbc
    simp only [Mixfix.eq.eqs, Bool.and_eq_true] at hab hbc ⊢
    exact ⟨mixopTrans a b c hab.1 hbc.1, mixopsTrans as bs cs hab.2 hbc.2⟩
end
/-- info: 'P4SpecTec.Refine.Representation.Source.mixopTrans' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixopTrans
#audit_axioms mixopTrans
/-- info: 'P4SpecTec.Refine.Representation.Source.mixopsTrans' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixopsTrans
#audit_axioms mixopsTrans

end P4SpecTec.Refine.Representation.Source
