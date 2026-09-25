import P4SpecTec.Lang.Al.Json
import P4SpecTec.Codegen.Emit

/-!
`lake exe p4spectec-gen <export.al.json> --lib <Lib> [--out DIR] [--update|--check]`:
the compiler's entry point. Reads an AL export, generates one `.lean`
module per upstream spec file plus the library root, and either writes
them (`--update`) or checks that the committed files are byte-identical
(`--check`, the default and the CI mode). Generated files are never
hand-edited.
-/

open P4SpecTec

/-- Parsed arguments. -/
structure Args where
  /-- The export path. -/
  exportPath : String := ""
  /-- The library name. -/
  lib : String := ""
  /-- The output directory. -/
  out : String := "."
  /-- Write instead of check. -/
  update : Bool := false

/-- Parse the command line. -/
def parseArgs : List String → Except String Args
  | [] => pure {}
  | "--lib" :: l :: rest => do pure { ← parseArgs rest with lib := l }
  | "--out" :: o :: rest => do pure { ← parseArgs rest with out := o }
  | "--update" :: rest => do pure { ← parseArgs rest with update := true }
  | "--check" :: rest => do pure { ← parseArgs rest with update := false }
  | e :: rest => do
    if e.startsWith "-" then throw s!"unknown option {e}"
    pure { ← parseArgs rest with exportPath := e }

/-- The entry point. -/
def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs argv with
    | .ok a => pure a
    | .error e => do IO.eprintln s!"p4spectec-gen: {e}"; return 2
  if args.exportPath.isEmpty || args.lib.isEmpty then
    IO.eprintln "usage: p4spectec-gen <export.al.json> --lib <Lib>"
    IO.eprintln "                     [--out DIR] [--update|--check]"
    return 2
  let spec ← Lang.Al.Json.readSpec args.exportPath
  let outs ← match Codegen.Emit.generate args.lib args.exportPath spec with
    | .ok o => pure o
    | .error e => do IO.eprintln s!"p4spectec-gen: {e}"; return 1
  let mut stale := 0
  for o in outs do
    let path := System.FilePath.mk args.out / o.path
    if args.update then
      if let some dir := path.parent then IO.FS.createDirAll dir
      IO.FS.writeFile path o.text
    else
      let current ← (IO.FS.readFile path).toBaseIO
      match current with
      | .ok text => if text != o.text then do IO.eprintln s!"stale: {o.path}"; stale := stale + 1
      | .error _ => do IO.eprintln s!"missing: {o.path}"; stale := stale + 1
  if stale > 0 then
    IO.eprintln s!"p4spectec-gen: {stale} file(s) differ; run with --update"
    return 1
  let verb := if args.update then "written" else "up to date"
  IO.println s!"p4spectec-gen: {outs.length} file(s) {verb}"
  return 0
