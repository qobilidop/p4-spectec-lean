import Lean.Data.Json.Parser
import P4SpecTec.Lang.Il.Json
import NanoP4Spec

/-!
`lake exe nano-p4-run <program.json>...`: the Lean side of the differential
harness (design section 5, rung 2). Each argument is a booted Nano-P4
program exported by `scripts/export-program.sh`; the program is decoded
into the generated `program` type and run through the generated
`Program_ok.run`. One line per program: `<path> <verdict>` where the
verdict is `pass` (succeeds, and its output typing context equals the
value in `<name>.outputs.json` when that file exists), `pass-outputs-differ`,
`fail` (an `Err` or `Unmatch`), `decode-error` or `read-error`. The
harness in `test/diff/` compares the verdicts with upstream's.
-/

open P4SpecTec P4SpecTec.Prelude

/-- Fuel for the value decoders: enough for any program of the corpus. -/
def fuel : Nat := 1000000

/-- The outputs upstream recorded for a program, if any: the `.outputs.json`
next to it holds the list of output values of `Program_ok`. -/
def expectedOutputs (path : String) : IO (Option (List Lang.Il.value)) := do
  let p := (path.dropEnd 5).toString ++ ".outputs.json"
  if !(← System.FilePath.pathExists p) then return none
  let json ← Util.Yojson.readFile p
  let vs ← IO.ofExcept (Util.Yojson.list Lang.Il.Json.value json)
  pure (some vs)

/-- Decode and type-check one program. -/
def check (path : String) : IO String := do
  let bytes ← (IO.FS.readBinFile path).toBaseIO
  match bytes with
  | Except.error _ => pure "read-error"
  | Except.ok bytes =>
    match Util.Yojson.parseBytes bytes >>= P4SpecTec.Lang.Il.Json.value with
    | Except.error _ => pure "decode-error"
    | Except.ok v =>
      match NanoP4Spec.program.ofValue fuel v with
      | none => pure "decode-error"
      | some prog =>
        match NanoP4Spec.Program_ok.run prog with
        | some (.ok tc) =>
          match ← expectedOutputs path with
          | some [expected] =>
            pure (if Runtime.Value.eq (toValue tc) expected then "pass"
              else "pass-outputs-differ")
          | some _ => pure "pass-outputs-differ"
          | none => pure "pass"
        | some (.error _) => pure "fail"
        | none => pure "diverge"

/-- Run every program named on the command line. -/
def main (args : List String) : IO UInt32 := do
  for path in args do
    IO.println s!"{path} {← check path}"
  return 0
