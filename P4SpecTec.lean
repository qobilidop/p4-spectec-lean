import P4SpecTec.Codegen.Emit
import P4SpecTec.Codegen.Env
import P4SpecTec.Codegen.Exp
import P4SpecTec.Codegen.Fmt
import P4SpecTec.Codegen.Funcs
import P4SpecTec.Codegen.Graph
import P4SpecTec.Codegen.Keywords
import P4SpecTec.Codegen.Names
import P4SpecTec.Codegen.Props
import P4SpecTec.Codegen.Rels
import P4SpecTec.Codegen.Types
import P4SpecTec.Domain.Atom
import P4SpecTec.Domain.Mixfix
import P4SpecTec.Interface.Builtin.Ints
import P4SpecTec.Interface.Builtin.Lists
import P4SpecTec.Interface.Builtin.Maps
import P4SpecTec.Interface.Builtin.Nats
import P4SpecTec.Interface.Builtin.Numerics
import P4SpecTec.Interface.Builtin.Sets
import P4SpecTec.Interface.Builtin.Texts
import P4SpecTec.Interface.P4.Unparse
import P4SpecTec.Lang.Al.Ast
import P4SpecTec.Lang.Al.Json
import P4SpecTec.Lang.Il.Ast
import P4SpecTec.Lang.Il.Json
import P4SpecTec.Lang.Xl.Bool
import P4SpecTec.Lang.Xl.Num
import P4SpecTec.Prelude
import P4SpecTec.Prelude.Eval
import P4SpecTec.Prelude.Extern
import P4SpecTec.Prelude.Iter
import P4SpecTec.Prelude.Num
import P4SpecTec.Prelude.Value
import P4SpecTec.Runtime.Value.Value
import P4SpecTec.Tactic.Audit
import P4SpecTec.Tactic.RunSound
import P4SpecTec.Util.Source
import P4SpecTec.Util.Yojson

/-!
# P4SpecTec

The core library: the deep embedding of P4-SpecTec's IL and AL
(`P4SpecTec.Lang.Il`, `P4SpecTec.Lang.Al`), its semantics ported from upstream's AL
interpreter (`P4SpecTec.Semantics`, from M2), the runtime the generated
code imports (`P4SpecTec.Prelude`), the code generator
(`P4SpecTec.Codegen`), and the tactic that discharges generated validation
theorems (`P4SpecTec.Tactic`, from M2).

Layout and principles: `docs/design.md`. A module whose path is an upstream
OCaml path, capitalised, mirrors that file (`Lang/Il/Ast.lean` mirrors
`lang/il/ast.ml`) under upstream's module name as its namespace, and says
so; `scripts/check-mirror.py` derives the pairs from the paths.
-/
