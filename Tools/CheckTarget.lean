import Lean.Util.Path
import P4SpecTec.Codegen.Coverage.Check
import P4SpecTec.Lang.Al.Json
import P4SpecTec.Interp.InterpAl.Interp

/-!
Runtime validation of the concrete NanoSwitch target claims against the compiled theorem
environment: each named theorem must exist with exactly the expected closed type and only the
allowed axioms. It also checks that the pinned Nano export declares no print hints, the table
under which the print-dependent certificates and the session theorems are stated. The
completion checker binds target-stage obligations to these claims only after this succeeds.
-/

open Lean Elab Term
open P4SpecTec P4SpecTec.Codegen.Coverage

/-- The target claims, in manifest order, with their exact expected types. -/
def targetClaims : List Claim :=
  [{ name := "NanoP4Target.externsContractHolds", kind := "target"
     direction := "externsContract"
     expectedType := "∀ {cfg : P4SpecTec.Interp_al.Interp.Config}, " ++
       "NanoP4Target.Reference cfg → NanoP4Spec.externsContract cfg" },
   { name := "NanoP4Target.referenceWitness", kind := "target"
     direction := "referenceInhabited"
     expectedType := "NanoP4Target.Reference " ++ config ++ " ∧ (" ++ config ++
       " : P4SpecTec.Interp_al.Interp.Config).printHints = []" },
   { name := "NanoP4Target.initializedSessionCorrespondence", kind := "composition"
     direction := "initializedTwoWaySessions"
     expectedType := sessionType "NanoP4Target.SessionRel" },
   { name := "NanoP4Target.sessionObservations", kind := "observations"
     direction := "sessionObservations"
     expectedType := sessionType ("(fun a b => P4SpecTec.Refine.Rel a.1 b.1 ∧ " ++
       "a.2.1 = P4SpecTec.BackendSim.NanoSwitch.Pipe.init_arch_state ∧ a.2.2 = b.2)") }]
where
  /-- The concrete reference configuration the session replay runs. -/
  config : String :=
    "{ guard := false, extern := P4SpecTec.BackendSim.NanoSwitch.Pipe.externInterface }"
  /-- Two-way session composition on the initialized environment under a relation; every
  name is fully qualified so a same-named local declaration cannot capture it. -/
  sessionType (relation : String) : String :=
    "∀ {cfg : P4SpecTec.Interp_al.Interp.Config}, NanoP4Target.Reference cfg → " ++
    "cfg.printHints = [] → " ++
    "∀ {vprogram : P4SpecTec.Lang.Il.value} {program : NanoP4Spec.program}, " ++
    "P4SpecTec.Refine.Rel vprogram program → " ++
    "∀ (rxs : List P4SpecTec.Runtime.Sim.Io.rx), " ++
    s!"(∀ fuel, P4SpecTec.Refine.Refines {relation} (NanoP4Target.referenceSession " ++
    "(NanoP4Target.relCall cfg NanoP4Spec.Environment.global fuel) vprogram rxs) " ++
    "(NanoP4Target.session program rxs)) ∧ " ++
    s!"P4SpecTec.Refine.Realizes {relation} (fun fuel => NanoP4Target.referenceSession " ++
    "(NanoP4Target.relCall cfg NanoP4Spec.Environment.global fuel) vprogram rxs) " ++
    "(NanoP4Target.session program rxs)"

/-- Check every target claim and the pinned print-hint table. -/
def runTargetChecks (env : Environment) : IO Unit := do
  Check.inEnvironment env "NanoP4Target" (targetClaims.forM Check.checkClaim)
  let spec ← Lang.Al.Json.readSpec "exports/nano-p4.al.json"
  let hints ← IO.ofExcept (P4.Unparse.hints_of_spec_al spec)
  unless hints.isEmpty do throw <| IO.userError "the pinned Nano export declares print hints"
  for claim in targetClaims do
    IO.println s!"[target] claim {claim.name}"
  IO.println s!"[target] {targetClaims.length} claims checked; pinned print hints empty"

/-- Check target claims through Lean's ordinary elaboration frontend. -/
def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "usage: check-target"
    return 2
  try
    -- Use Lean's ordinary frontend to initialize notation and elaborator extensions.
    let source := "import Tools.CheckTarget\nimport NanoP4Target\n" ++
      "run_cmd do\n  runTargetChecks (← Lean.getEnv)\n"
    let result ← IO.Process.output {
      cmd := ((← findSysroot) / "bin" / "lean").toString, args := #["--stdin"]
    } (some source)
    (← IO.getStdout).putStr result.stdout
    (← IO.getStderr).putStr result.stderr
    return result.exitCode
  catch error =>
    IO.eprintln s!"[target] {error}"
    return 1
