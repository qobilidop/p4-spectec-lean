import P4SpecTecTest.Oracle.P4.Sessions.Check
import P4SpecTecTest.Oracle.P4.Sessions.Generated
import P4SpecTec.Lang.Al.Json
import P4SpecTec.Interp.InterpAl.Interp

/-!
Not a mirror. The session worker: one process loads the full-P4 specification once and
then replays every observed session it is given, on both Lean legs of one target (v1model
or eBPF), answering one JSON line per session. The reference leg runs the AL interpreter
with the target's ported externs; the generated leg runs the generated library with the
target's typed extern instance over the same port. The reference leg's relation trampoline
is the interpreter's own relation evaluator over the same configuration, tied as upstream
ties its registered `call_rel`.
-/

namespace P4SpecTecTest.Diff.P4Sessions

open Lean P4SpecTec P4SpecTec.Prelude P4SpecTec.Interp_al P4SpecTec.BackendSim

/-- The interpreter's fuel bound; exhaustion is reported, never a verdict. -/
def fuel : Nat := 10000000

instance : Inhabited (Make.Spec StateEval) :=
  ⟨{ func := fun _ _ _ => throw .err, rel := fun _ _ => throw .err }⟩

/-- A target as the worker drives it: the replay's target, the extern interface of the
reference leg, and the generated leg's trampolines. -/
structure Arch where
  /-- The initializer and statement runner. -/
  target : Target
  /-- The reference leg's externs over its own evaluators. -/
  externs : Make.Spec StateEval → Interp.Extern StateEval
  /-- The generated leg's trampolines. -/
  generated : Make.Spec StateEval

/-- The targets by upstream's architecture name. -/
def arches : List (String × Arch) :=
  [("v1model", { target := v1modelTarget, externs := V1Model.Pipe.externInterface,
                 generated := Generated.spec }),
   ("ebpf", { target := ebpfTarget, externs := Ebpf.Pipe.externInterface,
              generated := Generated.ebpfSpec })]

/-- The reference leg's evaluators, whose configuration registers the target's externs
over these very evaluators: upstream's registered `call_func` and `call_rel`. -/
partial def interpSpec (g : Ctx.global) (hints : P4.Unparse.HEnv)
    (externs : Make.Spec StateEval → Interp.Extern StateEval) : Make.Spec StateEval :=
  -- The configuration is built under each callback, so the knot is tied lazily.
  let cfg : Unit → Interp.Config StateEval := fun _ =>
    { guard := false, extern := externs (interpSpec g hints externs), printHints := hints }
  { func := fun name targs values => Interp.do_eval_func fuel (cfg ()) g name targs values,
    rel := fun name values => Interp.do_eval_rel fuel (cfg ()) g name values }

/-- The reference leg. -/
def interpreterLeg (g : Ctx.global) (hints : P4.Unparse.HEnv)
    (externs : Make.Spec StateEval → Interp.Extern StateEval) : Leg :=
  let spec := interpSpec g hints externs
  { spec := { func := Make.call_func spec.func, rel := Make.call_rel spec.rel },
    representable := fun _ => none }

/-- The generated leg: the program must decode into the generated type and encode back. -/
def generatedLeg (spec : Make.Spec StateEval) : Leg :=
  { spec,
    representable := fun boot =>
      match P4Spec.p4program.ofValue Generated.decodeFuel boot with
      | none => some "the parsed program is outside the generated p4program type"
      | some program =>
        if Runtime.Value.eq (toValue program) boot then none
        else some "the decoded program does not encode back to the parsed value" }

/-- Answer one session: both legs' verdicts. -/
def answer (target : Target) (legs : List (String × Leg)) (path : String) : IO Json := do
  let bytes ← IO.FS.readBinFile path
  let json ← IO.ofExcept (Util.Yojson.parseBytes bytes)
  let obs ← IO.ofExcept (observationOf json)
  let verdicts := legs.map fun (label, leg) => (label, (verdict target leg obs).toJson)
  pure (Json.mkObj [("legs", Json.mkObj verdicts)])

end P4SpecTecTest.Diff.P4Sessions

/-- Load the specification, then answer session paths from stdin, one JSON line each;
`--arch NAME` selects the target (v1model unless given) and `--leg NAME` restricts the
answer to one leg. -/
def main (args : List String) : IO UInt32 := do
  let usage := "usage: p4-sessions-check <verified-p4.al.json> [--arch NAME] [--leg NAME]"
  let specPath :: options := args | IO.eprintln usage; return 1
  let mut selected : Option String := none
  let mut archName := "v1model"
  let mut options := options
  repeat
    match options with
    | [] => break
    | "--leg" :: leg :: rest => selected := some leg; options := rest
    | "--arch" :: arch :: rest => archName := arch; options := rest
    | _ => IO.eprintln usage; return 1
  let some arch := P4SpecTecTest.Diff.P4Sessions.arches.lookup archName
    | IO.eprintln "unknown target architecture"; return 1
  try
    let spec ← P4SpecTec.Lang.Al.Json.readSpec specPath
    let .ok cfg := P4SpecTec.Interp_al.Interp.Config.withPrintHints
      ({ guard := false } : P4SpecTec.Interp_al.Interp.Config P4SpecTec.Prelude.StateEval) spec
      | IO.eprintln "invalid full-P4 print hints"; return 1
    let .ok g := P4SpecTec.Interp_al.Interp.init spec
      | IO.eprintln "full-P4 initialization failed"; return 1
    let legs := [("interpreter",
                  P4SpecTecTest.Diff.P4Sessions.interpreterLeg g cfg.printHints arch.externs),
                 ("generated", P4SpecTecTest.Diff.P4Sessions.generatedLeg arch.generated)]
    let legs := legs.filter fun (label, _) => selected.all (· == label)
    if legs.isEmpty then IO.eprintln "unknown leg"; return 1
    let input ← IO.getStdin
    let output ← IO.getStdout
    output.putStrLn "{\"ready\":1}"
    output.flush
    repeat
      let line ← input.getLine
      if line.isEmpty then break
      let path := line.trimAscii.toString
      try
        output.putStrLn (← P4SpecTecTest.Diff.P4Sessions.answer arch.target legs path).compress
      catch error =>
        output.putStrLn (Lean.Json.mkObj [("error", Lean.Json.str error.toString)]).compress
      output.flush
    return 0
  catch error => IO.eprintln error.toString; return 1
