/-!
`lake exe p4spectec-gen [exports...] --out DIR [--update]`: the compiler's
entry point. Reads IL exports, generates one `.lean` module per upstream
spec file, and either writes them (`--update`) or checks that the committed
files are byte-identical to what it would write (the CI mode). Generated
files are never hand-edited.
-/

def main (_args : List String) : IO UInt32 := do
  IO.eprintln "p4spectec-gen: not implemented yet (see docs/design.md, milestone M1)"
  return 2
