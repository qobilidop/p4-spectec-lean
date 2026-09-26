import P4SpecTec.Lang.Il.Json

/-! Shared decoding of recorded upstream outputs for both Nano differential legs. -/

namespace P4SpecTecTest.Oracle.Nano.Replay

open P4SpecTec

/-- Read the optional `.outputs.json` sibling without changing parse or IO failures. -/
def expectedOutputs (path : String) : IO (Option (List Lang.Il.value)) := do
  let p := (path.dropEnd 5).toString ++ ".outputs.json"
  if !(← System.FilePath.pathExists p) then return none
  let json ← Util.Yojson.readFile p
  let vs ← IO.ofExcept (Util.Yojson.list Lang.Il.Json.value json)
  pure (some vs)

end P4SpecTecTest.Oracle.Nano.Replay
