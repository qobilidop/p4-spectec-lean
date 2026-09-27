import P4SpecTec.Refine.Representation.SourceRecord
import NanoP4Spec.«1-syntax»

/-! Distinguishing source grammar checks for namespaces, tags and parameter lookup. -/

namespace P4SpecTecTest.Refine.Representation.Source

open P4SpecTec P4SpecTec.Lang.Il P4SpecTec.Prelude P4SpecTec.Refine
open P4SpecTec.Refine.Representation

private def sameNameValue : Lang.Al.def :=
  Q.d (.VarD (Q.i "direction") (Q.t .TextT) [])

example : Representation.Source.declaration [sameNameValue, NanoP4Spec.direction.al]
    "direction" = some NanoP4Spec.direction.al := rfl

example : Representation.Source.Substitutes
    [("T", Lang.Il.typ'.TextT), ("T", .BoolT)].reverse
    (.VarT (Q.i "T") []) .BoolT := .bound _ _ rfl

example : ¬ Representation.Source.Valid [] (fun _ _ => False) (.NumT .NatT)
    (Runtime.Value.Make.int 0) := by
  intro valid
  cases valid with
  | nat _ _ shape => simp [Runtime.Value.Make.int, Runtime.Value.Make.mk] at shape

example : ¬ Representation.Source.Valid [] (fun _ _ => False) (.IterT (Q.t .TextT) .Opt)
    (Runtime.Value.Make.list .TextT []) := by
  intro valid
  cases valid <;> contradiction

private def recordFields : List typfield :=
  [(Q.a (.Keyword "number"), Q.t (.NumT .NatT)), (Q.a (.Keyword "text"), Q.t .TextT)]

private def recordDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "exampleRecord") [] (Q.dt (.StructT recordFields)) [])

private def recordType := Q.varT "exampleRecord" []
private def bytes := ByteText.ofString "bytes"
private def recordValue (fields : List (String × value)) := Runtime.Value.Make.str recordType fields
private def recordSource (v : value) :=
  Representation.Source.Valid [recordDeclaration] (fun _ _ => False) recordType v

example : recordSource (recordValue
    [("number", Runtime.Value.Make.nat 1), ("text", Runtime.Value.Make.text bytes)]) := by
  apply Representation.Source.Valid.record (Q.i "exampleRecord") [] [] recordFields
    (recordFields.map (·.2)) _
    [(Q.a (.Keyword "number"), Runtime.Value.Make.nat 1),
      (Q.a (.Keyword "text"), Runtime.Value.Make.text bytes)] rfl rfl
  · exact .cons rfl (.cons rfl .nil)
  · exact ⟨rfl, .cons (.num .NatT) (.cons .text .nil)⟩
  · exact .cons _ _ _ _ (.nat _ 1 rfl) (.cons _ _ _ _ (.text _ bytes rfl) .nil)

private theorem labelsOf (fields : List (String × value))
    (valid : recordSource (recordValue fields)) :
    List.Forall₂ (fun source actual => Domain.Atom.eq source.1.it actual.1.it = true)
      recordFields (fields.map (fun (label, v) => (Q.a (.Keyword label), v))) := by
  obtain ⟨types, _, actual, shape, labels, _⟩ :=
    Representation.Source.Valid.recordPayload (Q.i "exampleRecord") [] [] recordFields
      (recordValue fields) (by rfl) valid
  simp only [recordValue, Runtime.Value.Make.str, Runtime.Value.Make.mk] at shape
  have same := value'.StructV.inj shape
  exact same.symm ▸ labels

example : ¬ recordSource (recordValue
    [("text", Runtime.Value.Make.text bytes), ("number", Runtime.Value.Make.nat 1)]) := by
  intro valid
  have labels := labelsOf _ valid
  cases labels with
  | cons wrong _ => simp [Domain.Atom.eq, Domain.Atom.compare] at wrong

example : ¬ recordSource (recordValue
    [("number", Runtime.Value.Make.nat 1), ("number", Runtime.Value.Make.text bytes)]) := by
  intro valid
  have labels := labelsOf _ valid
  cases labels with
  | cons _ tail => cases tail with
    | cons wrong _ => simp [Domain.Atom.eq, Domain.Atom.compare] at wrong

example : ¬ recordSource (recordValue [("number", Runtime.Value.Make.nat 1)]) := by
  intro valid
  have labels := labelsOf _ valid
  cases labels with
  | cons _ tail => cases tail

end P4SpecTecTest.Refine.Representation.Source
