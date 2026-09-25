import Lean.Data.Json.Parser
import P4SpecTec.Lang.Il.Json
import P4SpecTec.Lang.Al.Json
import P4SpecTec.Interp.InterpAl.Interp

/-!
`lake exe nano-p4-interp <program.json>...`: the second leg of rung 2
(design section 5): the Lean port of the AL interpreter
(`P4SpecTec.Interp_al.Interp`) runs `Program_ok` on the deep term of each
booted Nano-P4 program, against the AL export of the spec itself, so the
trusted port is tested directly against upstream's verdicts. One line per
program: `<path> <verdict>` with the verdicts of `nano-p4-run` (`pass`,
`pass-outputs-differ`, `fail`, `diverge`, `decode-error`, `read-error`),
plus `init-error` when the spec does not load. `test/diff/run.py` drives
it beside `nano-p4-run`.
-/

open P4SpecTec P4SpecTec.Prelude

/-- Fuel for the interpreter: one unit per call, enough for the corpus. -/
def fuel : Nat := 10000000

/-- The outputs upstream recorded for a program, if any. -/
def expectedOutputs (path : String) : IO (Option (List Lang.Il.value)) := do
  let p := (path.dropEnd 5).toString ++ ".outputs.json"
  match ← (IO.FS.readFile p).toBaseIO with
  | Except.error _ => pure none
  | Except.ok text =>
    match Lean.Json.parse text >>= P4SpecTec.Util.Yojson.list P4SpecTec.Lang.Il.Json.value with
    | Except.error _ => pure none
    | Except.ok vs => pure (some vs)

/-- Decode and type-check one program through the interpreter. -/
def check (cfg : Interp_al.Interp.Config) (g : Interp_al.Ctx.global)
    (path : String) : IO String := do
  let debug := (← IO.getEnv "P4SPECTEC_INTERP_DEBUG").isSome
  let text ← (IO.FS.readFile path).toBaseIO
  match text with
  | Except.error _ => pure "read-error"
  | Except.ok text =>
    match Lean.Json.parse text >>= P4SpecTec.Lang.Il.Json.value with
    | Except.error _ => pure "decode-error"
    | Except.ok v =>
      match Interp_al.Interp.eval_rel fuel { cfg with debug } g "Program_ok" [v] with
      | some (.ok outs) =>
        match ← expectedOutputs path with
        | some expected =>
          pure (if outs.length == expected.length &&
              (outs.zip expected).all (fun (a, b) => Runtime.Value.eq a b) then "pass"
            else "pass-outputs-differ")
        | none => pure "pass"
      | some (.error e) =>
        -- the kind, on stderr, when debugging; the verdict stays `fail`
        if debug then IO.eprintln s!"{path}: {if e == .err then "err" else "unmatch"}"
        pure "fail"
      | none => pure "diverge"

/-- Load the spec, then run every program named on the command line. -/
def main (args : List String) : IO UInt32 := do
  let spec ← Lang.Al.Json.readSpec "exports/nano-p4.al.json"
  let .ok cfg := Interp_al.Interp.Config.withPrintHints {} spec
    | IO.eprintln "nano-p4-interp: invalid print hints"; return 1
  match Interp_al.Interp.init spec with
  | .error e =>
    IO.eprintln s!"nano-p4-interp: {e}"
    for path in args do IO.println s!"{path} init-error"
    return 1
  | .ok g =>
    for path in args do
      IO.println s!"{path} {← check cfg g path}"
    return 0
