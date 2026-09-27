import NanoP4Spec.Refinement.Equality

/-!
Actual generated dictionaries remain lawful for noninjective parameter encoders,
recursive values, aliases, and runtime extern extensions. No parameter `BEq`
dictionary is needed by the source pair's encoded-value equality.
-/

namespace P4SpecTecTest.Codegen.EqualityCertificates

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine.Representation

private inductive Erased where
  | first | second

private instance : ToValue Erased := ⟨fun _ => toValue true⟩

example : ValueBEq (NanoP4Spec.pair Erased Erased) := inferInstance
example : ValueBEq (NanoP4Spec.map Erased Erased) := inferInstance
example : ValueBEq NanoP4Spec.typeIR := inferInstance
example : ValueBEq NanoP4Spec.value := inferInstance

-- Parameter encoding is deliberately noninjective: generated source equality
-- observes the encodings, without assuming equality of the Lean values.
#guard (NanoP4Spec.pair.colon Erased.first Erased.first ==
  NanoP4Spec.pair.colon Erased.second Erased.second)

end P4SpecTecTest.Codegen.EqualityCertificates
