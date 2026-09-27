import P4SpecTec.Refine.Representation.Source

/-!
Inversion of independent source type substitution. Closed scalar and named fields
retain their declared syntax; a parameter receives exactly its selected binding.
Container inversion preserves the child derivation without equating source regions.
This is our own proof support, not an upstream mirror.
-/

namespace P4SpecTec.Refine.Representation.Source

open P4SpecTec.Lang.Il

/-- Boolean source fields cannot acquire another type through substitution. -/
theorem Substitutes.boolResult {bindings result}
    (h : Substitutes bindings .BoolT result) : result = .BoolT := by
  cases h
  rfl

/-- info: 'P4SpecTec.Refine.Representation.Source.Substitutes.boolResult' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Substitutes.boolResult
#audit_axioms Substitutes.boolResult

/-- Numeric source fields retain their declared numeric tag. -/
theorem Substitutes.numResult {bindings kind result}
    (h : Substitutes bindings (.NumT kind) result) : result = .NumT kind := by
  cases h
  rfl

/-- info: 'P4SpecTec.Refine.Representation.Source.Substitutes.numResult' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Substitutes.numResult
#audit_axioms Substitutes.numResult

/-- Byte-text source fields remain byte text after substitution. -/
theorem Substitutes.textResult {bindings result}
    (h : Substitutes bindings .TextT result) : result = .TextT := by
  cases h
  rfl

/-- info: 'P4SpecTec.Refine.Representation.Source.Substitutes.textResult' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Substitutes.textResult
#audit_axioms Substitutes.textResult

/-- An unbound closed named type preserves its head and empty argument list. -/
theorem Substitutes.namedResult {bindings result} (name : id)
    (absent : bindings.lookup name.it = none)
    (h : Substitutes bindings (.VarT name []) result) : result = .VarT name [] := by
  cases h with
  | bound name replacement found => simp [absent] at found
  | named name args instantiated unbound arguments =>
    cases arguments
    rfl

/-- info: 'P4SpecTec.Refine.Representation.Source.Substitutes.namedResult' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Substitutes.namedResult
#audit_axioms Substitutes.namedResult

/-- Empty parameter bindings preserve every closed named field without a depth premise. -/
theorem Substitutes.emptyNamedResult {result} (name : id)
    (h : Substitutes [] (.VarT name []) result) : result = .VarT name [] :=
  h.namedResult name rfl

/-- info: 'P4SpecTec.Refine.Representation.Source.Substitutes.emptyNamedResult' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Substitutes.emptyNamedResult
#audit_axioms Substitutes.emptyNamedResult

/-- Parameter substitution returns its binding without recursively rewriting that binding. -/
theorem Substitutes.boundResult {bindings result replacement} (name : id)
    (found : bindings.lookup name.it = some replacement)
    (h : Substitutes bindings (.VarT name []) result) : result = replacement := by
  cases h with
  | bound name replacement' found' => exact Option.some.inj (found'.symm.trans found)
  | named name args instantiated unbound arguments => simp [found] at unbound

/-- info: 'P4SpecTec.Refine.Representation.Source.Substitutes.boundResult' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Substitutes.boundResult
#audit_axioms Substitutes.boundResult

/-- Iteration substitution preserves the kind and supplies its precise child derivation. -/
theorem Substitutes.iterResult {bindings result} (element : typ) (kind : Lang.Il.iter)
    (h : Substitutes bindings (.IterT element kind) result) :
    ∃ instantiated : typ, result = .IterT instantiated kind ∧
      Substitutes bindings element.it instantiated.it := by
  cases h with
  | iter element instantiated kind argument => exact ⟨instantiated, rfl, argument⟩

/-- info: 'P4SpecTec.Refine.Representation.Source.Substitutes.iterResult' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Substitutes.iterResult
#audit_axioms Substitutes.iterResult

/-- Unbound named applications preserve their head and provide each argument substitution. -/
theorem Substitutes.namedArguments {bindings result} (name : id) (arguments : List typ)
    (absent : bindings.lookup name.it = none)
    (h : Substitutes bindings (.VarT name arguments) result) :
    ∃ instantiated, result = .VarT name instantiated ∧
      List.Forall₂ (fun a b : typ => Substitutes bindings a.it b.it) arguments instantiated := by
  cases h with
  | bound name replacement found => simp [absent] at found
  | named name arguments instantiated unbound fields => exact ⟨instantiated, rfl, fields⟩

/-- info: 'P4SpecTec.Refine.Representation.Source.Substitutes.namedArguments' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Substitutes.namedArguments
#audit_axioms Substitutes.namedArguments

end P4SpecTec.Refine.Representation.Source
