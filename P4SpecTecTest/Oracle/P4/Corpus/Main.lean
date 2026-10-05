import P4SpecTec.Lang.Al.Json
import P4SpecTec.Interp.InterpAl.Interp
import P4SpecTec.BackendSim.Placeholder
import P4SpecTecTest.Oracle.P4.Corpus.Check

/-!
Not a mirror. Corpus-v2 spec-once worker for the reference interpreter, independent of
published v1 replay. The shared checks are in `Corpus/Check.lean`.
-/

namespace P4SpecTecTest.Diff.P4Corpus

open Lean P4SpecTec P4SpecTec.Prelude P4SpecTec.Interp_al

/-- Initial fuel bound; exhausted computation is not an upstream failure. -/
def fuel : Nat := 10000000

/-- The reference interpreter as a leg, at a fuel bound. -/
def interpreterLeg (fuelLimit : Nat) (cfg : Interp.Config StateEval) (g : Ctx.global) : Leg :=
  fun name boot state => pure (Interp.evalRelState fuelLimit cfg g name [boot] state)

end P4SpecTecTest.Diff.P4Corpus

/-- Initialize one spec, then process bounded case-file paths from stdin. -/
def main (args : List String) : IO UInt32 := do
  let some (specPath, fuelLimit, maxBytes) := (do
    let (maxBytes, rest) ← P4SpecTecTest.Diff.P4Corpus.caseBound args
    match rest with
    | [path] => some (path, P4SpecTecTest.Diff.P4Corpus.fuel, maxBytes)
    | [path, "--fuel", n] => n.toNat?.map (path, ·, maxBytes)
    | _ => none)
    | IO.eprintln
        "usage: p4-corpus-worker <verified-p4.al.json> [--fuel N] [--max-case-bytes N]"
      return 1
  if fuelLimit > P4SpecTecTest.Diff.P4Corpus.fuel then
    IO.eprintln "fuel exceeds worker bound"; return 1
  try
    let spec ← P4SpecTec.Lang.Al.Json.readSpec specPath
    let .ok cfg := P4SpecTec.Interp_al.Interp.Config.withPrintHints
      ({ guard := false, extern := P4SpecTec.BackendSim.Placeholder.externInterface } :
        P4SpecTec.Interp_al.Interp.Config P4SpecTec.Prelude.StateEval) spec
      | IO.eprintln "invalid full-P4 print hints"; return 1
    let .ok globals := P4SpecTec.Interp_al.Interp.init spec
      | IO.eprintln "full-P4 initialization failed"; return 1
    P4SpecTecTest.Diff.P4Corpus.serve
      (P4SpecTecTest.Diff.P4Corpus.interpreterLeg fuelLimit cfg globals) maxBytes
    return 0
  catch error => IO.eprintln error.toString; return 1
