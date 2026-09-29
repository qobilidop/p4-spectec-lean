import Lean.Elab.Command
import NanoP4Spec.Refinement.Spec
import NanoP4Spec.Refinement.Representation.callableId
import NanoP4Spec.Refinement.Representation.direction
import NanoP4Spec.Refinement.Representation.id
import NanoP4Spec.Refinement.Representation.nameIR
import NanoP4Spec.Refinement.Representation.typeId
import P4SpecTec.Codegen.Certificates.Representation
import P4SpecTec.Codegen.Certificates.RepresentationRecursive
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveAdmission
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveCodec
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveTotality
import P4SpecTec.Refine.Representation.SourceCodec
import P4SpecTec.Refine.Representation.SourceExtern
import P4SpecTec.Refine.Representation.SourceSubst
import P4SpecTec.Tactic.Audit
import P4SpecTec.Tactic.CarrierInduction

/-! Source-derived SCC descriptors and exact generated encoder-helper identities. -/

namespace P4SpecTecTest.Codegen.RepresentationRecursive
open P4SpecTec P4SpecTec.Lang.Il P4SpecTec.Codegen P4SpecTec.Domain P4SpecTec.Refine
open P4SpecTec.Codegen.RepresentationRecursive

private def node := Q.d (.TypD (Q.i "node") [] (Q.dt (.VariantT
  [Q.tc (.Atom (Q.a (.Keyword "END"))) "node" [],
   Q.tc (.Seq [.Atom (Q.a (.Keyword "ENTRIES")),
     .Arg (Q.t (.IterT (Q.t (Q.varT "entry" [])) .List))]) "node" []])) [])
private def entry := Q.d (.TypD (Q.i "entry") [] (Q.dt (.StructT
  [(Q.a (.Keyword "CHILD"), Q.t (Q.varT "node" [])),
   (Q.a (.Keyword "TEXT"), Q.t .TextT)])) [])
private def env := Env.ofSpec "RecursiveFixture" [node, entry]

#guard (groupOf env "node").toOption.any (fun group =>
  group.length == 2 && group.contains "node" && group.contains "entry")
#guard (derive env (fun _ => none) "node").toOption.any fun plan =>
  plan.roots.length == 2 && plan.families.size == 4 && plan.dependencies.isEmpty &&
    plan.encoderHelpers.length == 1 &&
    plan.families.all (fun family => family.children.all (· < plan.families.size))

private def self := Q.d (.TypD (Q.i "self") [] (Q.dt (.VariantT
  [Q.tc (.Atom (Q.a (.Keyword "END"))) "self" [],
   Q.tc (.Seq [.Atom (Q.a (.Keyword "NEXT")), .Arg (Q.t (Q.varT "self" []))])
     "self" []])) [])
#guard (groupOf (Env.ofSpec "Self" [self]) "self").toOption == some ["self"]
#guard (derive (Env.ofSpec "Self" [self]) (fun _ => none) "self").isOk

private def loop := Q.d (.TypD (Q.i "loop") []
  (Q.dt (.PlainT (Q.t (.IterT (Q.t (Q.varT "loop" [])) .List)))) [])
#guard !(derive (Env.ofSpec "Loop" [loop]) (fun _ => none) "loop").isOk

private def growing := Q.d (.TypD (Q.i "growing") [Q.i "K"] (Q.dt (.VariantT
  [Q.tc (.Seq [.Atom (Q.a (.Keyword "GROW")),
    .Arg (Q.t (Q.varT "growing" [Q.t (.IterT (Q.t (Q.varT "K" [])) .List)]))])
    "growing" []])) [])
private def growRoot := Q.d (.TypD (Q.i "growRoot") [] (Q.dt (.VariantT
  [Q.tc (.Seq [.Atom (Q.a (.Keyword "LOOP")),
    .Arg (Q.t (Q.varT "growRoot" []))]) "growRoot" [],
   Q.tc (.Seq [.Atom (Q.a (.Keyword "PAYLOAD")),
    .Arg (Q.t (Q.varT "growing" [Q.t (Q.varT "growRoot" [])]))]) "growRoot" []])) [])
#guard !(derive (Env.ofSpec "Growing" [growing, growRoot]) (fun _ => none) "growRoot").isOk

private def actualEnv := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec
private def known (name : String) : Option RepresentationFields.NominalContract :=
  if ["direction", "id", "callableId", "nameIR", "typeId"].contains name then
    some ⟨"NanoP4Spec." ++ name ++ (if name == "direction" then ".sourceCodec" else ".codec"),
      "fun _ => True"⟩
  else none

private def knownTotal (name : String) : Option RepresentationTotals.TotalContract :=
  (known name).map fun contract => ⟨contract, "fun _ => True.intro"⟩

private def actualPlan := derive actualEnv known "typeIR"
#guard actualPlan.isOk
#guard actualPlan.toOption.any fun plan =>
  plan.roots.length == 5 &&
    ["parameterIR", "fieldTypeIR", "externMethodTypeDefIR", "typeIR",
      "externMethodTypeDefEnv"].all (fun name => plan.members.contains name) &&
    plan.families.all (fun family => family.children.all (· < plan.families.size))

-- Runtime-only alternatives are described separately and never added to source declarations.
#guard (derive { actualEnv with representation := { rawExternTypes := ["typeIR"] } }
  known "typeIR").toOption.any fun plan =>
    plan.families.any fun family => family.runtimeExtended && family.declaration.isSome

open Lean Elab Command in
run_cmd do
  let plan ← match actualPlan with
    | .ok plan => pure plan
    | .error message => throwError "{message}"
  for helper in plan.encoderHelpers do
    unless (← getEnv).contains helper.toName do
      throwError "descriptor names an absent actual encoder helper: {helper}"

open P4SpecTec.Prelude
open Lean Elab Command in
run_cmd do
  let plan ← match actualPlan with
    | .ok plan => pure plan
    | .error message => throwError "{message}"
  let bundle ← match declarations actualEnv plan "ActualSourceFamilies" with
    | .ok declarations => pure declarations
    | .error message => throwError "{message}"
  let totals ← match totalityDeclarations actualEnv plan "ActualSourceFamilies" knownTotal with
    | .ok totals => pure totals
    | .error message => throwError "{message}"
  let scopedBundle := [Std.Format.text "namespace _root_.NanoP4Spec"] ++ bundle ++ [totals] ++
    [Std.Format.text "end _root_.NanoP4Spec"]
  for declaration in scopedBundle do
    let output := render declaration
    let commands := if output.startsWith "mutual" then [output] else output.splitOn "\n\n"
    for text in commands do
      let command ← match Parser.runParserCategory (← getEnv) `command text with
        | .ok command => pure command
        | .error message => throwError "{text}\n{message}"
      elabCommand command

-- Nonrecursive leaf admissions are supplied independently; these fixtures emit no leaf codec.
private def valueEnv := { actualEnv with representation := { rawExternTypes := ["value"] } }
private def valuePlan := derive valueEnv (fun _ => some ⟨"unprovedLeaf", "fun _ => True"⟩) "value"
#guard valuePlan.isOk
#guard valuePlan.toOption.any fun plan =>
  !(totalityDeclarations valueEnv plan "RejectedRuntimeTotals" knownTotal).isOk

open Lean Elab Command in
run_cmd do
  let plan ← match valuePlan with
    | .ok plan => pure plan
    | .error message => throwError "{message}"
  let families ← match familyDeclarations plan "ValueSourceFamilies" with
    | .ok families => pure families
    | .error message => throwError "{message}"
  let predicates ← match admissionDeclarations valueEnv plan "ValueSourceFamilies" with
    | .ok predicates => pure predicates
    | .error message => throwError "{message}"
  let some (_, valueIndex) := plan.roots.find? (fun (name, _) => name == "value")
    | throwError "value source family is absent"
  let some (_, fieldIndex) := plan.roots.find? (fun (name, _) => name == "fieldValue")
    | throwError "fieldValue source family is absent"
  let checks := ["namespace ValueSourceFamilies",
    s!"private theorem runtimeRejected (state : ExternValue) : " ++
      s!"¬ AdmittedF{valueIndex} (NanoP4Spec.value.runtimeExtern state) := by " ++
      "intro accepted; cases accepted",
    "#audit_axioms runtimeRejected",
    s!"private theorem nestedRuntimeRejected (state : ExternValue) : " ++
      s!"¬ AdmittedF{fieldIndex} (NanoP4Spec.fieldValue.semi " ++
      "(NanoP4Spec.value.runtimeExtern state) (ByteText.ofString \"\")) := by\n" ++
      "  intro accepted\n  cases accepted with\n  | semi _ _ head _ => cases head",
    "#audit_axioms nestedRuntimeRejected", "end ValueSourceFamilies"]
  let texts := (render families).splitOn "\n\n" ++ predicates.map render ++ checks
  for text in texts do
    let command ← match Parser.runParserCategory (← getEnv) `command text with
      | .ok command => pure command
      | .error message => throwError "{text}\n{message}"
    elabCommand command

-- The runtime closure is exactly the declared types that can contain a runtime `value`.
#guard (RepresentationCertificates.runtimeClosure actualEnv).isEmpty
#guard (RepresentationCertificates.runtimeClosure valueEnv).mergeSort (· ≤ ·) ==
  ["blockEvalLayer", "dataValue", "evalContext", "fieldValue", "frame", "globalEvalLayer",
    "headerValue", "localEvalLayer", "structValue", "value"]

-- The runtime profile admits the raw extern, directly and nested, and its totality is total.
private def runtimeEnv := { valueEnv with runtimeProfile := true }
private def leafTotal (_ : String) : Option RepresentationTotals.TotalContract :=
  some ⟨⟨"unprovedLeaf", "fun _ => True"⟩, "fun _ => True.intro"⟩
#guard valuePlan.toOption.any fun plan =>
  !(totalityDeclarations valueEnv plan "RejectedRuntimeTotals" leafTotal).isOk &&
    (totalityDeclarations runtimeEnv plan "RuntimeTotals" leafTotal).isOk

open Lean Elab Command in
run_cmd do
  let plan ← match valuePlan with
    | .ok plan => pure plan
    | .error message => throwError "{message}"
  let families ← match familyDeclarations plan "ValueRuntimeFamilies" with
    | .ok families => pure families
    | .error message => throwError "{message}"
  let predicates ← match admissionDeclarations runtimeEnv plan "ValueRuntimeFamilies" with
    | .ok predicates => pure predicates
    | .error message => throwError "{message}"
  let some (_, valueIndex) := plan.roots.find? (fun (name, _) => name == "value")
    | throwError "value source family is absent"
  let some (_, fieldIndex) := plan.roots.find? (fun (name, _) => name == "fieldValue")
    | throwError "fieldValue source family is absent"
  let checks := ["namespace ValueRuntimeFamilies",
    s!"private theorem runtimeAdmitted (state : ExternValue) : " ++
      s!"AdmittedF{valueIndex} (NanoP4Spec.value.runtimeExtern state) := .runtimeExtern state",
    "#audit_axioms runtimeAdmitted",
    s!"private theorem nestedRuntimeAdmitted (state : ExternValue) : " ++
      s!"AdmittedF{fieldIndex} (NanoP4Spec.fieldValue.semi " ++
      "(NanoP4Spec.value.runtimeExtern state) (ByteText.ofString \"\")) :=\n" ++
      "  .semi _ _ (.runtimeExtern state) trivial",
    "#audit_axioms nestedRuntimeAdmitted", "end ValueRuntimeFamilies"]
  let texts := (render families).splitOn "\n\n" ++ predicates.map render ++ checks
  for text in texts do
    let command ← match Parser.runParserCategory (← getEnv) `command text with
      | .ok command => pure command
      | .error message => throwError "{text}\n{message}"
    elabCommand command

end P4SpecTecTest.Codegen.RepresentationRecursive
