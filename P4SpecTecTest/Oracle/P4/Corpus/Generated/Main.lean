import P4SpecTecTest.Oracle.P4.Corpus.Check
import P4SpecTecTest.Oracle.P4.Generated.Externs

/-!
Not a mirror. The corpus-v2 worker for the generated full-P4 library: the booted
program is decoded into the generated `p4program` type and run through the generated
`Program_ok.run` and `Program_inst.run` from the observed fresh counter. Generated
recursion has no fuel, so a run that does not terminate does not answer; the driver's
response deadline bounds it, and reports a timeout, never a verdict.
-/

namespace P4SpecTecTest.Diff.P4Corpus.Generated

open P4SpecTec P4SpecTec.Prelude P4SpecTecTest.Diff.P4Generated

/-- The generated library as a leg. A booted program outside the generated `p4program`
type, or one whose decoding does not encode back to it, is reported, not evaluated. -/
def leg : Leg := fun name boot state => do
  let some program := P4Spec.p4program.ofValue decodeFuel boot
    | throw "the booted program is outside the generated p4program type"
  unless Runtime.Value.eq (toValue program) boot do
    throw "the decoded program does not encode back to the booted value"
  match name with
  | "Program_ok" =>
    pure ((P4Spec.Program_ok.run program state).map fun (result, state) =>
      (result.map fun ir => [toValue ir], state))
  | "Program_inst" =>
    pure ((P4Spec.Program_inst.run program state).map fun (result, state) =>
      (result.map fun (layer, store) => [toValue layer, toValue store], state))
  | _ => throw s!"{name}: not a replayed relation"

end P4SpecTecTest.Diff.P4Corpus.Generated

/-- Process bounded case-file paths from stdin on the generated library. -/
def main (args : List String) : IO UInt32 := do
  let some (maxBytes, []) := P4SpecTecTest.Diff.P4Corpus.caseBound args
    | IO.eprintln "usage: p4-corpus-worker-gen [--max-case-bytes N]"; return 1
  try
    P4SpecTecTest.Diff.P4Corpus.serve P4SpecTecTest.Diff.P4Corpus.Generated.leg maxBytes
    return 0
  catch error => IO.eprintln error.toString; return 1
