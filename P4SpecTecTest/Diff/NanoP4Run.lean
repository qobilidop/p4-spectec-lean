import Lean.Data.Json.Parser
import P4SpecTec.IL.Json
import NanoP4Spec

/-!
`lake exe nano-p4-run <program.json>...`: the Lean side of the differential
harness (design section 5, rung 2). Each argument is a booted Nano-P4
program exported by `scripts/export-program.sh`; the program is decoded
into the generated `program` type and run through the generated
`Program_ok.run`. One line per program: `<path> <verdict>` where the
verdict is `pass`, `fail`, `decode-error` or `read-error`. The harness in
`test/diff/` compares the verdicts with upstream's.
-/

open P4SpecTec P4SpecTec.Prelude

/-- Fuel for the executable relations: enough for any program of the corpus. -/
def fuel : Nat := 1000000

/-- Decode and type-check one program. -/
def check (path : String) : IO String := do
  let text ← (IO.FS.readFile path).toBaseIO
  match text with
  | Except.error _ => pure "read-error"
  | Except.ok text =>
    match Lean.Json.parse text >>= P4SpecTec.IL.Json.value with
    | Except.error _ => pure "decode-error"
    | Except.ok v =>
      match NanoP4Spec.program.ofValue fuel v with
      | none => pure "decode-error"
      | some prog =>
        match NanoP4Spec.Program_ok.run fuel prog with
        | some _ => pure "pass"
        | none => pure "fail"

/-- Run every program named on the command line. -/
def main (args : List String) : IO UInt32 := do
  for path in args do
    IO.println s!"{path} {← check path}"
  return 0
