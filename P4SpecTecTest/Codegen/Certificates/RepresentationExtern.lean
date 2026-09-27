import Lean.Elab.Command
import NanoP4Spec.Refinement.Spec
import P4SpecTec.Codegen.Certificates.RepresentationExtern
import P4SpecTec.Refine.Representation.SourceExtern
import P4SpecTec.Refine.Representation.SourceVariant

/-! Actual opaque Nano source codecs, kept distinct from runtime-only value alternatives. -/

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Codegen

namespace NanoP4Spec

open Lean Elab Command in
run_cmd do
  let env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec
  let output ← match RepresentationExterns.declarations env NanoP4Spec.objectState.al with
    | .ok output => pure output
    | .error message => throwError "{message}"
  for text in (output.pretty.replace ".codec" ".testCodec").splitOn "\n\n" do
    let command ← match Parser.runParserCategory (← getEnv) `command text with
      | .ok command => pure command
      | .error message => throwError "{text}\n{message}"
    elabCommand command

/-- info: 'NanoP4Spec.objectState.testCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms objectState.testCodec

private def valueConstructors : List Lang.Il.typcase :=
  match NanoP4Spec.value.al.it with
  | .TypD _ _ definition _ => match definition.it with
    | .VariantT constructors => constructors
    | _ => []
  | _ => []

-- The source extern domain admits arbitrary target JSON for the declared objectState.
example (json : Lean.Json) : Representation.Source.Valid NanoP4Spec.spec
    Representation.Source.externDomain (Q.varT "objectState" [])
    (Runtime.Value.Make.extern (Q.varT "objectState" []) json) :=
  .external (Q.i "objectState") _ (by rfl) ⟨json, rfl⟩

-- It does not silently add a raw-extern source constructor to the defined value variant.
theorem rawExternNotSourceValue (json : Lean.Json) :
    ¬ Representation.Source.Valid NanoP4Spec.spec Representation.Source.externDomain
      (Q.varT "value" []) (Runtime.Value.Make.extern (Q.varT "value" []) json) := by
  intro valid
  obtain ⟨_, _, _, _, _, shape, _, _⟩ :=
    Representation.Source.Valid.variantPayload (Q.i "value") [] [] valueConstructors
      _ (by rfl) valid
  cases shape

/-- info: 'NanoP4Spec.rawExternNotSourceValue' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rawExternNotSourceValue

end NanoP4Spec
