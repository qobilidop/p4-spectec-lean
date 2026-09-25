import P4SpecTec.Util.Source
import P4SpecTec.Util.Json
import P4SpecTec.Xl.Num
import P4SpecTec.Xl.Bool
import P4SpecTec.Domain.Atom
import P4SpecTec.Domain.Mixfix
import P4SpecTec.IL.Ast
import P4SpecTec.IL.Json
import P4SpecTec.AL.Ast
import P4SpecTec.AL.Json
import P4SpecTec.Prelude
import P4SpecTec.Prelude.Value
import P4SpecTec.Prelude.Extern
import P4SpecTec.Prelude.Num
import P4SpecTec.Prelude.Iter
import P4SpecTec.Prelude.Builtins.Texts
import P4SpecTec.Prelude.Builtins.Lists
import P4SpecTec.Prelude.Builtins.Sets
import P4SpecTec.Prelude.Builtins.Maps
import P4SpecTec.Prelude.Builtins.Nats
import P4SpecTec.Prelude.Builtins.Ints
import P4SpecTec.Prelude.Builtins.Numerics
import P4SpecTec.Codegen.Emit
import P4SpecTec.Codegen.Rels
import P4SpecTec.Codegen.Funcs
import P4SpecTec.Codegen.Exp
import P4SpecTec.Codegen.Types
import P4SpecTec.Codegen.Fmt
import P4SpecTec.Codegen.Graph
import P4SpecTec.Codegen.Env
import P4SpecTec.Codegen.Names
import P4SpecTec.Codegen.Keywords

/-!
# P4SpecTec

The core library: the deep embedding of P4-SpecTec's IL and AL
(`P4SpecTec.IL`, `P4SpecTec.AL`), its semantics ported from upstream's AL
interpreter (`P4SpecTec.Semantics`, from M2), the runtime the generated
code imports (`P4SpecTec.Prelude`), the code generator
(`P4SpecTec.Codegen`), and the tactic that discharges generated validation
theorems (`P4SpecTec.Tactic`, from M2).

Layout and principles: `docs/design.md`. Every module under `IL/`, `AL/`,
`Xl/`, `Domain/`, `Util/Source`, `Semantics/` and `Prelude/Builtins/`
mirrors one upstream OCaml file and says which.
-/
