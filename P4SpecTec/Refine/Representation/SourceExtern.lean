import P4SpecTec.Refine.Representation.SourceCodec
import P4SpecTec.Runtime.Value.Match

/-!
Declared opaque source types use the upstream extern-value shape: arbitrary JSON
inside `ExternV`. The source grammar still requires an actual external declaration.
The source profile adds no runtime-only alternative to a declared source variant; a runtime
profile names the declared types whose runtime carriers also hold a raw `ExternV`.
-/

namespace P4SpecTec.Refine.Representation.Source

open P4SpecTec.Lang.Il P4SpecTec.Prelude

/-- The source domain admits no runtime-only value at any declared type. -/
theorem externDomainNoRuntime (name : String) (v : value) : ¬ externDomain.runtime name v :=
  fun admitted => nomatch admitted.1

/-- info: 'P4SpecTec.Refine.Representation.Source.externDomainNoRuntime' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externDomainNoRuntime
#audit_axioms externDomainNoRuntime

/-- The checked runtime membership rule for a declared extern is exactly this domain.
Positive fuel suffices; neither the JSON contents nor source metadata are restricted. -/
theorem externCheckedIff (findType : Runtime.Value.Match.FindTypdef)
    (findFunction : Runtime.Value.Match.FindFuncChecked) (name : id) (fuel : Nat)
    (v : value) (declared : findType name.it = some .Extern) :
    (Runtime.Value.Match.sub_checked findType findFunction (fuel + 1)
      (Util.Source.mkPhrase (.VarT name [])) v).run = some (.ok true) ↔
      externDomain.external name.it v := by
  rcases v with ⟨contents, note, location⟩
  cases contents <;>
    simp [Runtime.Value.Match.sub_checked, Util.Source.mkPhrase, declared,
      externDomain, runtimeDomain, Shape.extern, pure, ExceptT.pure]

/-- info: 'P4SpecTec.Refine.Representation.Source.externCheckedIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externCheckedIff
#audit_axioms externCheckedIff

/-- An actual external declaration has no alias, record or variant body. -/
theorem externalBodyNone {spec : Lang.Al.spec} {name : String}
    (declared : external spec name = true) : body spec name = none := by
  unfold external at declared
  unfold body
  cases found : declaration spec name with
  | none => simp [found] at declared
  | some definition =>
    cases definition with
    | mk contents note location =>
      cases contents <;> simp_all

/-- info: 'P4SpecTec.Refine.Representation.Source.externalBodyNone' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externalBodyNone
#audit_axioms externalBodyNone

/-- Declared opaque source types admit exactly extern JSON, independently of decoding. -/
theorem externalIff {spec : Lang.Al.spec} (name : id)
    (declared : external spec name.it = true) (v : value) :
    Valid spec externDomain (.VarT name []) v ↔ Shape.extern v := by
  have absent := externalBodyNone declared
  constructor
  · intro valid
    cases valid <;> simp_all [externDomain, runtimeDomain]
  · intro payload
    exact .external name v declared payload

/-- info: 'P4SpecTec.Refine.Representation.Source.externalIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externalIff
#audit_axioms externalIff

/-- The actual extern carrier and dictionaries cover the complete declared source extern. -/
theorem externalCodec {spec : Lang.Al.spec} (name : id)
    (declared : external spec name.it = true) :
    Codec (Valid spec externDomain (.VarT name [])) (fun _ : ExternValue => True) :=
  Codec.sourceIff (fun v => (externalIff name declared v).symm) Representation.externCodec

/-- info: 'P4SpecTec.Refine.Representation.Source.externalCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externalCodec
#audit_axioms externalCodec

end P4SpecTec.Refine.Representation.Source
