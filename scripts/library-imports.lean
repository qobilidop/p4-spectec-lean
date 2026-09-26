import Lean.Elab.Import
import Lean.Data.Json.Printer

/-! Parse import headers with the pinned Lean parser, without elaborating project modules. -/

/-- Emit source dependencies as JSON, rejecting errors the dependency CLI discards. -/
def main (args : List String) : IO UInt32 := do
  let searchPath ← Lean.getSrcSearchPath
  let mut rows := #[]
  for source in args do
    let (imports, _, messages) ← Lean.Elab.parseImports (← IO.FS.readFile source) source
    if messages.hasErrors then
      for message in messages.toList do
        (← IO.getStderr).putStrLn (← message.toString)
      return 1
    let mut dependencies := #[]
    for dependency in imports do
      let path ← Lean.findLean searchPath dependency.module
      dependencies := dependencies.push (.str path.toString)
    rows := rows.push (Lean.Json.mkObj [
      ("source", .str source), ("dependencies", .arr dependencies)])
  IO.println (Lean.Json.arr rows).compress
  return 0
