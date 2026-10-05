import P4SpecTec.Lang.Al.Json
import P4SpecTec.Interp.InterpAl.Interp
import P4SpecTecTest.Oracle.P4.Replay.Check

/-!
Replay four pinned full-P4 oracle cases through the Lean AL interpreter. The
Python driver validates source provenance and the fixed fixture before handing
this executable a typed JSON observation bundle. Successful relation outputs
are compared semantically, and every completed run checks the exact fresh
counter after boot and evaluation.
-/

namespace P4SpecTecTest.Diff.P4Interp

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Interp_al

/-- A bounded interpreter fuel, distinct from an upstream mismatch. -/
def fuel : Nat := 10000000

/-! The pinned `backend-sim/placeholder.ml` externs used by AL validation.
Other extern operations stay hard failures; this is not a P4 simulator. -/
private def placeholderExtern : Interp.Extern StateEval where
  eval_extern_rel := fun _ _ _ => throw .err
  eval_extern_func := fun name _ _ =>
    let typName := match name with
      | "init_objectState" => some "objectState"
      | "init_archState" => some "archState"
      | _ => none
    match typName with
    | some typ => pure (Runtime.Value.Make.extern
        (.VarT (P4SpecTec.Util.Source.mkPhrase typ) []) Lean.Json.null)
    | none => throw .err

/-- The reference interpreter as a leg, at a fuel bound. -/
def leg (fuelLimit : Nat) (cfg : Interp.Config StateEval) (g : Ctx.global) : P4Replay.Leg :=
  fun name boot state => pure (Interp.evalRelState fuelLimit cfg g name [boot] state)

end P4SpecTecTest.Diff.P4Interp

/-- Validate and replay the bounded full-P4 AL observations. -/
def main (args : List String) : IO UInt32 := do
  let some (path, testMutations) := (match args with
    | [path] => some (path, false)
    | [path, "--sensitivity"] => some (path, true)
    | _ => none)
    | IO.eprintln "usage: p4-interp-replay <bundle.json> [--sensitivity]"; return 1
  try
    let bundle ← P4SpecTec.Util.Yojson.readFile path
    let spec ← P4SpecTec.Lang.Al.Json.readSpec "exports/p4.al.json"
    let debug := (← IO.getEnv "P4SPECTEC_INTERP_DEBUG").isSome
    let .ok cfg := P4SpecTec.Interp_al.Interp.Config.withPrintHints
      ({ guard := false, debug, extern := P4SpecTecTest.Diff.P4Interp.placeholderExtern } :
        P4SpecTec.Interp_al.Interp.Config
        P4SpecTec.Prelude.StateEval) spec
      | IO.eprintln "[p4-interp] invalid print hints"; return 1
    let .ok globals := P4SpecTec.Interp_al.Interp.init spec
      | IO.eprintln "[p4-interp] full-P4 spec initialization failed"; return 1
    let leg := P4SpecTecTest.Diff.P4Interp.leg P4SpecTecTest.Diff.P4Interp.fuel cfg globals
    match P4SpecTecTest.Diff.P4Replay.check leg bundle with
    | .error message => IO.eprintln s!"[p4-interp] {message}"; return 1
    | .ok lines =>
        for line in lines do IO.println s!"[p4-interp] {line}"
        if testMutations then
          match P4SpecTecTest.Diff.P4Replay.sensitivity leg
              (P4SpecTecTest.Diff.P4Interp.leg 0 cfg globals) bundle with
          | .error message => IO.eprintln s!"[p4-interp] {message}"; return 1
          | .ok _ => IO.println "[p4-interp] nine Lean sensitivity mutations rejected"
        return 0
  catch e =>
    IO.eprintln s!"[p4-interp] {e}"
    return 1
