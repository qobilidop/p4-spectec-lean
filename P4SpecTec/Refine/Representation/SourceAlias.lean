import P4SpecTec.Refine.Representation.SourceSubst

/-!
Source aliases are interpreted through their actual declaration and finite substitution,
independently of generated decoders. These rules preserve arbitrary value metadata.
This is our own proof support, not an upstream mirror.
-/

namespace P4SpecTec.Refine.Representation.Source

open P4SpecTec.Lang.Il

/-- A source type with a plain body cannot also be an external declaration. -/
theorem externalFalseOfBody {spec name parameters definition}
    (declared : body spec name = some (parameters, definition)) :
    external spec name = false := by
  unfold body at declared
  unfold external
  cases hd : declaration spec name with
  | none => simp [hd] at declared
  | some d =>
    cases hk : d.it <;> simp [hd, hk] at declared ⊢

/-- info: 'P4SpecTec.Refine.Representation.Source.externalFalseOfBody' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externalFalseOfBody
#audit_axioms externalFalseOfBody

/-- A monomorphic plain alias has exactly the grammar of its substitution-stable body. -/
theorem plainAliasIff {spec externalDomain} (name : id) (definition : typ)
    (declared : body spec name.it = some ([], .PlainT definition))
    (stable : ∀ result, Substitutes [] definition.it result → result = definition.it)
    (identity : Substitutes [] definition.it definition.it) (v : value) :
    Valid spec externalDomain (.VarT name []) v ↔ Valid spec externalDomain definition.it v := by
  constructor
  · intro h
    cases h with
    | «alias» name arguments parameters definition' instantiated v found fields payload =>
      have heq := Option.some.inj (found.symm.trans declared)
      cases heq
      obtain ⟨_, fields⟩ := fields
      cases fields with
      | cons sub tail =>
        cases tail
        have hs := stable _ sub
        simpa only [hs] using payload
    | record name arguments parameters sourceFields instantiated v valueFields found =>
      simp [declared] at found
    | variant name arguments parameters cases constructor instantiated v tree found =>
      simp [declared] at found
    | external name v found payload =>
      simp [externalFalseOfBody declared] at found
  · intro h
    exact .alias name [] [] definition definition v declared
      ⟨rfl, .cons identity .nil⟩ h

/-- info: 'P4SpecTec.Refine.Representation.Source.plainAliasIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms plainAliasIff
#audit_axioms plainAliasIff

/-- A text alias admits precisely the source byte-text tag, including arbitrary metadata. -/
theorem textAliasIff {spec externalDomain} (name : id) (definition : typ)
    (declared : body spec name.it = some ([], .PlainT definition))
    (text : definition.it = .TextT) (v : value) :
    Valid spec externalDomain (.VarT name []) v ↔ Shape.text v := by
  have plain := plainAliasIff (externalDomain := externalDomain) name definition declared
    (by intro result h; rw [text] at h; simpa only [text] using h.textResult)
    (by rw [text]; exact .text) v
  rw [plain, text]
  constructor
  · intro h
    cases h with
    | text v t shape => exact ⟨t, shape⟩
  · rintro ⟨t, shape⟩
    exact .text v t shape

/-- info: 'P4SpecTec.Refine.Representation.Source.textAliasIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms textAliasIff
#audit_axioms textAliasIff

/-- Named type arguments depend on their syntax, not on their source locations. -/
theorem Valid.arguments {spec externalDomain} {name : id} {args args' : List typ} {v}
    (same : args.map (·.it) = args'.map (·.it))
    (valid : Valid spec externalDomain (.VarT name args) v) :
    Valid spec externalDomain (.VarT name args') v := by
  have lengths : args.length = args'.length := by
    simpa only [List.length_map] using congrArg List.length same
  cases valid with
  | «alias» name args parameters definition instantiated v declared fields payload =>
    apply Valid.alias name args' parameters definition instantiated v declared
    · simpa only [instantiatedFields, ← lengths, ← same] using fields
    · exact payload
  | record name args parameters sourceFields instantiated v valueFields
      declared shape labels fields payload =>
    apply Valid.record name args' parameters sourceFields instantiated v valueFields
      declared shape labels
    · simpa only [instantiatedFields, ← lengths, ← same] using fields
    · exact payload
  | variant name args parameters cases constructor instantiated v tree
      declared member shape mixop fields payload =>
    apply Valid.variant name args' parameters cases constructor instantiated v tree
      declared member shape mixop
    · simpa only [instantiatedFields, ← lengths, ← same] using fields
    · exact payload
  | external name v declared payload =>
    have empty : args' = [] := by cases args' <;> simp_all
    subst args'
    exact .external name v declared payload

/-- info: 'P4SpecTec.Refine.Representation.Source.Valid.arguments' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Valid.arguments
#audit_axioms Valid.arguments

/-- A plain source alias exposes its precise finite substitution and valid payload. -/
theorem Valid.plainPayload {spec externalDomain} {name : id} {args parameters} {definition : typ}
    {v : value} (declared : body spec name.it = Option.some (parameters, .PlainT definition))
    (valid : Valid spec externalDomain (.VarT name args) v) :
    ∃ instantiated : typ, instantiatedFields parameters args [definition] [instantiated] ∧
      Valid spec externalDomain instantiated.it v := by
  cases valid with
  | «alias» name args parameters' definition' instantiated v found fields payload =>
    have heq := Option.some.inj (found.symm.trans declared)
    cases heq
    exact ⟨instantiated, fields, payload⟩
  | record name args parameters sourceFields instantiated v valueFields found =>
    simp [declared] at found
  | variant name args parameters cases constructor instantiated v tree found =>
    simp [declared] at found
  | external name v found payload =>
    simp [externalFalseOfBody declared] at found

/-- info: 'P4SpecTec.Refine.Representation.Source.Valid.plainPayload' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Valid.plainPayload
#audit_axioms Valid.plainPayload

/-- Positional source validity ignores each field type's outer source location. -/
theorem Values.types {spec externalDomain} {types types' : List typ} {values}
    (same : List.Forall₂ (fun a b : typ => a.it = b.it) types types')
    (valid : Values spec externalDomain types values) :
    Values spec externalDomain types' values := by
  induction same generalizing values with
  | nil => cases valid; exact .nil
  | cons h hs ih =>
    cases valid with
    | cons type v types values head tail => exact .cons _ v _ _ (h ▸ head) (ih tail)

/-- info: 'P4SpecTec.Refine.Representation.Source.Values.types' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Values.types
#audit_axioms Values.types

/-- Iteration domains depend on element syntax, not its outer source location. -/
theorem Valid.iterElement {spec externalDomain} {element element' : typ} {kind v}
    (same : element.it = element'.it)
    (valid : Valid spec externalDomain (.IterT element kind) v) :
    Valid spec externalDomain (.IterT element' kind) v := by
  cases valid with
  | list element v values shape elements =>
    apply Valid.list element' v values shape
    apply elements.types
    clear elements shape
    induction values with
    | nil => exact .nil
    | cons v vs ih => exact .cons same ih
  | none element v shape => exact .none element' v shape
  | some element v inner shape payload => exact .some element' v inner shape (same ▸ payload)

/-- info: 'P4SpecTec.Refine.Representation.Source.Valid.iterElement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Valid.iterElement
#audit_axioms Valid.iterElement

/-- Named source domains ignore the head identifier's source region. -/
theorem Valid.nominalName {spec externalDomain} {name name' : id} {args : List typ} {v}
    (same : name.it = name'.it) (valid : Valid spec externalDomain (.VarT name args) v) :
    Valid spec externalDomain (.VarT name' args) v := by
  cases valid with
  | «alias» name args parameters definition instantiated v declared fields payload =>
    exact .alias name' args parameters definition instantiated v (same ▸ declared) fields payload
  | record name args parameters sourceFields instantiated v valueFields
      declared shape labels fields payload =>
    exact .record name' args parameters sourceFields instantiated v valueFields
      (same ▸ declared) shape labels fields payload
  | variant name args parameters cases constructor instantiated v tree
      declared member shape mixop fields payload =>
    exact .variant name' args parameters cases constructor instantiated v tree
      (same ▸ declared) member shape mixop fields payload
  | external name v declared payload =>
    exact .external name' v (same ▸ declared) (same ▸ payload)

/-- info: 'P4SpecTec.Refine.Representation.Source.Valid.nominalName' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Valid.nominalName
#audit_axioms Valid.nominalName

/-- A plain alias has the body's domain when empty substitution preserves source validity.
Only domain implication is required; instantiated source-region metadata may differ. -/
theorem plainAliasDomainIff {spec externalDomain} (name : id) (definition : typ)
    (declared : body spec name.it = some ([], .PlainT definition))
    (normalize : ∀ actual : typ, Substitutes [] definition.it actual.it →
      ∀ v, Valid spec externalDomain actual.it v → Valid spec externalDomain definition.it v)
    (identity : Substitutes [] definition.it definition.it) (v : value) :
    Valid spec externalDomain (.VarT name []) v ↔ Valid spec externalDomain definition.it v := by
  constructor
  · intro h
    obtain ⟨actual, fields, payload⟩ := h.plainPayload declared
    obtain ⟨_, substitutions⟩ := fields
    cases substitutions with
    | cons substitution rest =>
      cases rest
      exact normalize actual substitution v payload
  · intro payload
    exact .alias name [] [] definition definition v declared ⟨rfl, .cons identity .nil⟩ payload
/-- info: 'P4SpecTec.Refine.Representation.Source.plainAliasDomainIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms plainAliasDomainIff
#audit_axioms plainAliasDomainIff

end P4SpecTec.Refine.Representation.Source
