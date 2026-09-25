/-!
# P4SpecTec

The core library: the deep embedding of P4-SpecTec's IL (`P4SpecTec.IL`),
its semantics ported from upstream's AL interpreter (`P4SpecTec.Semantics`),
the runtime the generated code imports (`P4SpecTec.Prelude`), the code
generator (`P4SpecTec.Codegen`), and the tactic that discharges generated
validation theorems (`P4SpecTec.Tactic`).

Layout and principles: `docs/design.md`. Every module under `Semantics/` and
`Prelude/Builtins/` mirrors one upstream OCaml file and says which.
-/
