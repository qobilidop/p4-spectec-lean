import P4SpecTec.Interface.P4.Unparse
import P4SpecTecTest.Quote
import NanoP4Spec.Refinement.Spec

/-! Compare the actual compiled Nano-P4 quotation with the current export. -/

/-- Check the Nano quotation and the source prerequisite for no-hint printing. -/
def main : IO UInt32 := do
  let source ← P4SpecTec.Lang.Al.Json.readSpec "exports/nano-p4.al.json"
  match P4SpecTecTest.Quote.compareSpecs source NanoP4Spec.spec with
  | .error e => IO.eprintln e; return 1
  | .ok n => IO.println s!"[quotes] {n} definitions match the decoded export"
  -- The no-hint print contract requires the actual source environment, not only
  -- equality of normalized quotations (which intentionally erases hint metadata).
  for (name, spec) in [("decoded", source), ("compiled", NanoP4Spec.spec)] do
    match P4SpecTec.P4.Unparse.hints_of_spec_al spec with
    | .ok [] => pure ()
    | .ok _ =>
      IO.eprintln s!"[quotes] {name} Nano print hints are nonempty; revise the print contract"
      return 1
    | .error e =>
      IO.eprintln s!"[quotes] {name} Nano print hints failed: {e}"
      return 1
  IO.println "[quotes] decoded and compiled Nano print environments are empty"
  return 0
