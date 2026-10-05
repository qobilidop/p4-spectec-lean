import P4SpecTec.Codegen.QuoteCheck
import P4Spec.Refinement.Spec

/-! Compare the actual compiled full-P4 quotation with the current export. -/

/-- Check the full-P4 quotation against the decoded export. -/
def main : IO UInt32 := do
  let source ← P4SpecTec.Lang.Al.Json.readSpec "exports/p4.al.json"
  match P4SpecTec.Codegen.QuoteCheck.compareSpecs source P4Spec.spec with
  | .error e => IO.eprintln e; return 1
  | .ok n => IO.println s!"[quotes] {n} full-P4 definitions match the decoded export"
  return 0
