import P4SpecTec.Prelude.Extern
import P4SpecTec.Refine.ValueOrder

/-!
Full ordering and normalization regressions. Values can differ in metadata or in
unobserved carrier fields. Extern canonicalization is not itself order-preserving
when compared again, so the contracts must retain original compressed payloads.
-/

namespace P4SpecTecTest.ValueOrder

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Refine.ValueOrder

-- Executable regression: Json.compress is a Lean partial definition, so this
-- concrete printer observation is not advertised as a kernel theorem.
#guard Runtime.Value.compare (Runtime.Value.Make.extern .TextT (.str ""))
    (Runtime.Value.Make.extern .TextT (.arr #[])) == .lt &&
  Runtime.Value.compare (canon (Runtime.Value.Make.extern .TextT (.str "")))
    (canon (Runtime.Value.Make.extern .TextT (.arr #[]))) == .gt

/-- Arbitrary nested extern payloads and source notes preserve the complete ordering. -/
theorem nestedMetadata (a b : Lean.Json) (na nb : Lang.Il.typ') :
    Runtime.Value.compare
      (Runtime.Value.Make.list na [Runtime.Value.Make.extern na a])
      (Runtime.Value.Make.list nb [Runtime.Value.Make.extern nb b]) =
    valueCompare ([ExternValue.mk a] : List ExternValue) [ExternValue.mk b] := by
  exact compareOfRel (by rfl) (by rfl)

/-- info: 'P4SpecTecTest.ValueOrder.nestedMetadata' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nestedMetadata
#audit_axioms nestedMetadata

/-- An extra carrier field is deliberately not an observation. -/
structure Tagged where
  key : Nat
  ghost : Bool
  deriving DecidableEq

instance : ToValue Tagged := ⟨fun x => toValue x.key⟩

/-- Stable sorting plus last-adjacent retention preserves the actual chosen representatives. -/
theorem duplicateRepresentatives :
    Builtin.Sets.normalize ([⟨2, false⟩, ⟨1, true⟩, ⟨2, true⟩, ⟨1, false⟩] : List Tagged) =
      [⟨1, false⟩, ⟨2, true⟩] := by
  cbv

/-- info: 'P4SpecTecTest.ValueOrder.duplicateRepresentatives' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms duplicateRepresentatives
#audit_axioms duplicateRepresentatives

/-- Idempotence needs neither carrier equality nor injectivity of its encoder. -/
theorem arbitraryRepresentatives (xs : List Tagged) :
    Builtin.Sets.normalize (Builtin.Sets.normalize xs) = Builtin.Sets.normalize xs :=
  normalizeIdempotent xs

/-- info: 'P4SpecTecTest.ValueOrder.arbitraryRepresentatives' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms arbitraryRepresentatives
#audit_axioms arbitraryRepresentatives

/-- Unbounded nested source values use the same total, transitive comparison. -/
theorem nestedTransitivity (a b c : List (Option ExternValue))
    (hab : (valueCompare a b).isLE) (hbc : (valueCompare b c).isLE) :
    (valueCompare a c).isLE :=
  compareTrans (toValue a) (toValue b) (toValue c) hab hbc

/-- info: 'P4SpecTecTest.ValueOrder.nestedTransitivity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nestedTransitivity
#audit_axioms nestedTransitivity

end P4SpecTecTest.ValueOrder
