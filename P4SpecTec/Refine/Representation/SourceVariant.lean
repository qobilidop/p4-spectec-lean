import P4SpecTec.Refine.Representation.SourceAlias
import P4SpecTec.Refine.Representation.SourceMixfix

/-!
Independent constructor domains and inversion of actual source variant declarations.
This is our own proof support, not an upstream mirror.
-/

namespace P4SpecTec.Refine.Representation.Source
open P4SpecTec.Lang.Il P4SpecTec.Domain

/-- A declared constructor shape with independently valid positional source fields. -/
def ConstructorDomain (spec : Lang.Al.spec) (externalDomain : String → value → Prop)
    (constructor : typcase) (fields : List typ) (v : value) : Prop :=
  ∃ tree : Mixfix.t value, v.it = .CaseV tree ∧
    Mixfix.eq_mixop tree constructor.nottyp.it = true ∧
    Values spec externalDomain fields (Mixfix.args tree)

/-- A source variant exposes its actual case, parameter substitution and valid fields. -/
theorem Valid.variantPayload {spec externalDomain} (name : id) (args : List typ)
    (parameters : List tparam) (constructors : List typcase) (v : value)
    (declared : Source.body spec name.it = Option.some (parameters, .VariantT constructors))
    (valid : Valid spec externalDomain (.VarT name args) v) :
    ∃ constructor ∈ constructors, ∃ fields,
      instantiatedFields parameters args (Mixfix.args constructor.nottyp.it) fields ∧
      ConstructorDomain spec externalDomain constructor fields v := by
  cases valid with
  | «alias» name args parameters definition instantiated v found =>
    simp [declared] at found
  | variant name args parameters cases constructor instantiated v tree
      found member shape mixop fields payload =>
    have heq := Option.some.inj (found.symm.trans declared)
    cases heq
    exact ⟨constructor, member, instantiated, fields, tree, shape, mixop, payload⟩
  | external name v found payload =>
    have absent := externalFalseOfBody declared
    simp [absent] at found

/-- info: 'P4SpecTec.Refine.Representation.Source.Valid.variantPayload' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Valid.variantPayload
#audit_axioms Valid.variantPayload

/-- Actual constructor membership and field instantiation establish the named source domain. -/
theorem ConstructorDomain.valid {spec externalDomain} (name : id) (args : List typ)
    (parameters : List tparam) (constructors : List typcase) (constructor : typcase)
    (fields : List typ) (v : value)
    (declared : Source.body spec name.it = Option.some (parameters, .VariantT constructors))
    (member : constructor ∈ constructors)
    (instantiated : instantiatedFields parameters args (Mixfix.args constructor.nottyp.it) fields)
    (valid : ConstructorDomain spec externalDomain constructor fields v) :
    Valid spec externalDomain (.VarT name args) v := by
  obtain ⟨tree, shape, mixop, payload⟩ := valid
  exact .variant name args parameters constructors constructor fields v tree declared
    member shape mixop instantiated payload

/-- info: 'P4SpecTec.Refine.Representation.Source.ConstructorDomain.valid' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ConstructorDomain.valid
#audit_axioms ConstructorDomain.valid

end P4SpecTec.Refine.Representation.Source
