import P4SpecTecTest.Quote
import NanoP4Spec.Refinement.Spec

/-! Compare the actual compiled Nano-P4 quotation with the current export. -/

/-- Fail when the compiled quoted specification differs from the decoded export. -/
def main : IO UInt32 := do
  let source ← P4SpecTec.Lang.Al.Json.readSpec "exports/nano-p4.al.json"
  match P4SpecTecTest.Quote.compareSpecs source NanoP4Spec.spec with
  | .error e => IO.eprintln e; return 1
  | .ok n => IO.println s!"[quotes] {n} definitions match the decoded export"; return 0
