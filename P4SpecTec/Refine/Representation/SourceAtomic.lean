import P4SpecTec.Refine.Representation.SourceAlias

/-!
The atomic-variant codec domain agrees with the independent finite source grammar
when the actual monomorphic declaration contains only atomic constructors.
This is our own proof support, not an upstream mirror.
-/

namespace P4SpecTec.Refine.Representation.Source

open P4SpecTec.Lang.Il P4SpecTec.Domain

/-- An entire quoted atomic family has the same domain in both source grammar interfaces. -/
theorem atomicIff {spec externalDomain annotations} (d : Lang.Al.def) (name : id)
    (definition : deftyp) (cases : List typcase)
    (declarationShape : d.it = .TypD name [] definition annotations)
    (bodyShape : definition.it = .VariantT cases)
    (declared : body spec name.it = some ([], .VariantT cases))
    (atomic : ∀ c ∈ cases, ∃ a, c.nottyp.it = .Atom a) (v : value) :
    Valid spec externalDomain (.VarT name []) v ↔ atomVariant d v := by
  have kinds : atomKinds d = cases.filterMap (fun c => match c.nottyp.it with
      | .Atom a => some a.it | _ => none) := by
    simp only [atomKinds, declarationShape, bodyShape]
    rfl
  constructor
  · intro valid
    cases valid with
    | record name args parameters sourceFields instantiated v valueFields found =>
      simp [declared] at found
    | «alias» name args parameters definition instantiated v found =>
      simp [declared] at found
    | variant name args parameters cases' constructor instantiated v tree
        found member shape mixop fields payload =>
      have heq := Option.some.inj (found.symm.trans declared)
      cases heq
      obtain ⟨a, ha⟩ := atomic constructor member
      rw [ha] at mixop
      cases tree with
      | Atom b =>
        have same : b.it = a.it := by
          simpa [Mixfix.eq_mixop, Mixfix.eq, Atom.eq, Atom.compare_eq_iff] using mixop
        refine ⟨b, shape, ?_⟩
        rw [kinds]
        apply List.mem_filterMap.mpr
        exact ⟨constructor, member, by simp [ha, same]⟩
      | _ =>
        simp [Mixfix.eq_mixop, Mixfix.eq] at mixop
    | external name v found payload =>
      simp [externalFalseOfBody declared] at found
  · rintro ⟨a, shape, member⟩
    rw [kinds] at member
    obtain ⟨constructor, hc, hfilter⟩ := List.mem_filterMap.mp member
    obtain ⟨b, hb⟩ := atomic constructor hc
    have same : b.it = a.it := by simpa [hb] using hfilter
    refine .variant name [] [] cases constructor [] v (.Atom a) declared hc shape ?_ ?_ ?_
    · simp [hb, Mixfix.eq_mixop, Mixfix.eq, Atom.eq, Atom.compare_eq_iff, same]
    · simp [instantiatedFields, hb, Mixfix.args]
    · simpa only [Mixfix.args] using (Values.nil (spec := spec)
        (externalDomain := externalDomain))

/-- info: 'P4SpecTec.Refine.Representation.Source.atomicIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms atomicIff
#audit_axioms atomicIff

end P4SpecTec.Refine.Representation.Source
