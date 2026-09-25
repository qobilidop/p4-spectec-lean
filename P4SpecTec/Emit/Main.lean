/-!
`lake exe p4spectec-emit`: pretty-prints the syntax the code generator
produces to `.lean` files, for reading and debugging. The generated
libraries themselves are elaborated directly by `spectec_import`; this
executable exists only so a human can read what was generated.
-/

def main (_args : List String) : IO UInt32 := do
  IO.eprintln "p4spectec-emit: not implemented yet (see docs/design.md, milestone M1)"
  return 2
