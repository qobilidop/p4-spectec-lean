import P4SpecTec.Refine.Representation.SourceAlias
import P4SpecTec.Refine.Representation.SourceMixfix

/-!
Independent constructor domains and inversion of actual source variant declarations.
This is our own proof support, not an upstream mirror.
-/

namespace P4SpecTec.Refine.Representation.Source
open P4SpecTec.Lang.Il P4SpecTec.Domain

/-- A declared constructor shape with independently valid positional source fields. -/
def ConstructorDomain (spec : Lang.Al.spec) (externalDomain : Domain)
    (constructor : typcase) (fields : List typ) (v : value) : Prop :=
  ∃ tree : Mixfix.t value, v.it = .CaseV tree ∧
    Mixfix.eq_mixop tree constructor.nottyp.it = true ∧
    Values spec externalDomain fields (Mixfix.args tree)

/-- A source variant exposes its actual case, parameter substitution and valid fields. -/
theorem Valid.variantPayload {spec externalDomain} (name : id) (args : List typ)
    (parameters : List tparam) (constructors : List typcase) (v : value)
    (declared : Source.body spec name.it = Option.some (parameters, .VariantT constructors))
    (valid : Valid spec externalDomain (.VarT name args) v)
    (sourceOnly : Domain.SourceOnly externalDomain name.it := by source_only) :
    ∃ constructor ∈ constructors, ∃ fields,
      instantiatedFields parameters args (Mixfix.args constructor.nottyp.it) fields ∧
      ConstructorDomain spec externalDomain constructor fields v := by
  cases valid with
  | record name args parameters sourceFields instantiated v valueFields found =>
    simp [declared] at found
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
  | runtime name args v payload => exact absurd payload (sourceOnly v)

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

/-- Pointwise independent field-domain implications transport positional source validity. -/
theorem Values.domains {spec externalDomain} {types types' : List typ} {values}
    (transfer : List.Forall₂ (fun a b : typ => ∀ v,
      Valid spec externalDomain a.it v → Valid spec externalDomain b.it v) types types')
    (valid : Values spec externalDomain types values) :
    Values spec externalDomain types' values := by
  induction transfer generalizing values with
  | nil => cases valid; exact .nil
  | cons h hs ih =>
    cases valid with
    | cons type v types values head tail => exact .cons _ v _ _ (h v head) (ih tail)


/-- info: 'P4SpecTec.Refine.Representation.Source.Values.domains' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Values.domains
#audit_axioms Values.domains

/-- A single declared source constructor exposes fields in proved independent field domains. -/
theorem Valid.singleConstructor {spec externalDomain} (name : id) (arguments : List typ)
    (parameters : List tparam) (constructor : typcase) (fields : List typ) (v : value)
    (declared : body spec name.it = Option.some (parameters, .VariantT [constructor]))
    (normalize : ∀ instantiated,
      instantiatedFields parameters arguments (Mixfix.args constructor.nottyp.it) instantiated →
      List.Forall₂ (fun a b : typ => ∀ v,
        Valid spec externalDomain a.it v → Valid spec externalDomain b.it v) instantiated fields)
    (valid : Valid spec externalDomain (.VarT name arguments) v)
    (sourceOnly : Domain.SourceOnly externalDomain name.it := by source_only) :
    ConstructorDomain spec externalDomain constructor fields v := by
  obtain ⟨selected, member, instantiated, subs, tree, shape, matching, payload⟩ :=
    valid.variantPayload name arguments parameters [constructor] v declared sourceOnly
  have same := List.mem_singleton.mp member
  subst selected
  exact ⟨tree, shape, matching, payload.domains (normalize instantiated subs)⟩

/-- info: 'P4SpecTec.Refine.Representation.Source.Valid.singleConstructor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Valid.singleConstructor
#audit_axioms Valid.singleConstructor

end P4SpecTec.Refine.Representation.Source
