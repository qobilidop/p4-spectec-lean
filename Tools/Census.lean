import P4SpecTec.Codegen.Census

/-! Command-line capability census over an exported specification. -/

open P4SpecTec P4SpecTec.Codegen.Census

/-- Check or refresh a deterministic capability report. -/
def main (args : List String) : IO UInt32 := do
  let [input, mode, output] := args
    | IO.eprintln "usage: p4spectec-census <export> --update|--check <report.json>"; return 2
  if mode != "--update" && mode != "--check" then
    IO.eprintln "expected --update or --check"; return 2
  let spec ← Lang.Al.Json.readSpec input
  let report := (census spec).pretty ++ "\n"
  if mode == "--update" then IO.FS.writeFile output report
  else if (← IO.FS.readFile output) != report then
    IO.eprintln s!"stale census: {output}"; return 1
  IO.println s!"[census] {spec.length} definitions; {output} {mode}"
  return 0
