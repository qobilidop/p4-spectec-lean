import Lean.Environment
import Lean.CoreM

/-!
Listing a library's constants for the refinement tactics without waiting for other proofs.
`Environment.constants` forces the kernel environment, which joins every declaration still
being elaborated in parallel, so reading it would make each theorem of a module wait for the
previous ones. Imported constants come from the module data instead, and the current
module's from `Environment.getLocalConstantInfos`, whose names and kinds are known before
their proofs.
-/

namespace P4SpecTec.Tactic

open Lean

/-- The imported constants in `env` whose names extend `pre`, with their kinds. Distinct
environments in one process may have different imports, so the scan is environment-local. -/
def importedUnderIn (env : Environment) (pre : Name) : Array (Name × ConstantKind) := Id.run do
  let mut out := #[]
  -- a constant realized in several modules is listed once, as in the kernel environment
  let mut seen : Std.HashSet Name := {}
  for data in env.header.moduleData do
    for info in data.constants do
      if pre.isPrefixOf info.name && !seen.contains info.name then
        seen := seen.insert info.name
        out := out.push (info.name, ConstantKind.ofConstantInfo info)
  return out

/-- The imported constants whose names extend `pre`, with their kinds. -/
def importedUnder (pre : Name) : CoreM (Array (Name × ConstantKind)) := do
  return importedUnderIn (← getEnv) pre

/-- The constants of the current module whose names extend `pre`, with their kinds, including
declarations whose proofs are still being elaborated. -/
def localUnder (pre : Name) : CoreM (Array (Name × ConstantKind)) := do
  let mut out := #[]
  -- the nested declarations of a theorem are its proof's; listing them would wait for it
  for info in ← (← getEnv).getLocalConstantInfos (skipTheoremSubDecls := true) do
    if pre.isPrefixOf info.name then out := out.push (info.name, info.kind)
  pure out

/-- Every constant, local or imported, whose name extends `pre`, with its kind. -/
def constantsUnder (pre : Name) : CoreM (Array (Name × ConstantKind)) :=
  return (← localUnder pre) ++ (← importedUnder pre)

end P4SpecTec.Tactic
