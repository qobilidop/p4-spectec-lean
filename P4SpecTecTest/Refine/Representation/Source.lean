import P4SpecTec.Refine.Representation.Source
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

end P4SpecTecTest.Refine.Representation.Source
