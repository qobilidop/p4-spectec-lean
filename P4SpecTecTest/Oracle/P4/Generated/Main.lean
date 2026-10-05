import P4SpecTecTest.Oracle.P4.Replay.Check
import P4Spec

/-!
Replay the four pinned full-P4 oracle cases through the generated library: the
booted program is decoded into the generated `p4program` type and run through the
generated `Program_ok.run` and `Program_inst.run` from the observed fresh counter.
The checks are the reference interpreter leg's (`Replay/Check.lean`): semantic
outputs and the exact counter after evaluation. Generated recursion has no fuel,
so a run that does not terminate does not return.
-/

namespace P4SpecTecTest.Diff.P4Generated

open P4SpecTec P4SpecTec.Prelude

/-- Fuel for the value decoders: enough for any program of the bundle. -/
def decodeFuel : Nat := 1000000

/-- The pinned `backend-sim/placeholder.ml` externs, as the interpreter leg has them:
the two state initializers return a null extern value, every other operation is a hard
error. -/
instance placeholderExterns : P4Spec.Externs where
  ExternFunctionCall_eval_lctk := fun _ _ _ => StateEval.run (throw .err)
  «$init_objectState» := fun _ _ _ _ => StateEval.run (pure ExternValue.null)
  «$init_archState» := StateEval.run (pure ExternValue.null)
  ExternFunctionCall_eval := fun _ _ _ _ => StateEval.run (throw .err)
  ExternMethodCall_eval := fun _ _ _ _ _ => StateEval.run (throw .err)

/-- The generated library as a leg. The decoded program must encode back to the booted
value, so that agreement on a rejected program is not agreement about another input. -/
def leg : P4Replay.Leg := fun name boot state => do
  let some program := P4Spec.p4program.ofValue decodeFuel boot
    | throw s!"{name}: the booted program is outside the generated p4program type"
  unless Runtime.Value.eq (toValue program) boot do
    throw s!"{name}: the decoded program does not encode back to the booted value"
  match name with
  | "Program_ok" =>
    pure ((P4Spec.Program_ok.run program state).map fun (result, state) =>
      (result.map fun ir => [toValue ir], state))
  | "Program_inst" =>
    pure ((P4Spec.Program_inst.run program state).map fun (result, state) =>
      (result.map fun (layer, store) => [toValue layer, toValue store], state))
  | _ => throw s!"{name}: not a replayed relation"

/-- A leg that never returns within its bound, for the exhaustion check: generated
recursion has no fuel to withhold. -/
def exhausted : P4Replay.Leg := fun _ _ _ => pure none

end P4SpecTecTest.Diff.P4Generated

/-- Validate and replay the bounded full-P4 observations on the generated library. -/
def main (args : List String) : IO UInt32 := do
  let some (path, testMutations) := (match args with
    | [path] => some (path, false)
    | [path, "--sensitivity"] => some (path, true)
    | _ => none)
    | IO.eprintln "usage: p4-gen-replay <bundle.json> [--sensitivity]"; return 1
  try
    let bundle ← P4SpecTec.Util.Yojson.readFile path
    let leg := P4SpecTecTest.Diff.P4Generated.leg
    match P4SpecTecTest.Diff.P4Replay.check leg bundle with
    | .error message => IO.eprintln s!"[p4-generated] {message}"; return 1
    | .ok lines =>
        for line in lines do IO.println s!"[p4-generated] {line}"
        if testMutations then
          match P4SpecTecTest.Diff.P4Replay.sensitivity leg
              P4SpecTecTest.Diff.P4Generated.exhausted bundle with
          | .error message => IO.eprintln s!"[p4-generated] {message}"; return 1
          | .ok _ => IO.println "[p4-generated] nine observation mutations rejected"
        return 0
  catch e =>
    IO.eprintln s!"[p4-generated] {e}"
    return 1
