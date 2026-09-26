import P4SpecTec.Codegen.Emit
import P4SpecTec.Codegen.Coverage
import P4SpecTec.Codegen.Coverage.Check
import P4SpecTec.BackendSim.Core.Object
import P4SpecTec.BackendSim.Core.Func
import P4SpecTec.BackendSim.SpecImpl.Func
import P4SpecTec.BackendSim.SpecImpl.Unpack
import P4SpecTec.BackendSim.NanoSwitch.Pipe
import P4SpecTec.Runtime.Sim.Io
import P4SpecTec.Codegen.Attempt
import P4SpecTec.Codegen.Env
import P4SpecTec.Codegen.Exp
import P4SpecTec.Codegen.Fmt
import P4SpecTec.Codegen.Funcs
import P4SpecTec.Codegen.Graph
import P4SpecTec.Codegen.Keywords
import P4SpecTec.Codegen.Names
import P4SpecTec.Codegen.Mode
import P4SpecTec.Codegen.Props
import P4SpecTec.Codegen.StateProps
import P4SpecTec.Codegen.PrintHints
import P4SpecTec.Codegen.Reify
import P4SpecTec.Codegen.Rels
import P4SpecTec.Codegen.Types
import P4SpecTec.Codegen.Validate
import P4SpecTec.Codegen.StateValidate
import P4SpecTec.Domain.Atom
import P4SpecTec.Domain.Mixfix
import P4SpecTec.Interface.Builtin.Call
import P4SpecTec.Interface.Builtin.Ints
import P4SpecTec.Interface.Builtin.Lists
import P4SpecTec.Interface.Builtin.Maps
import P4SpecTec.Interface.Builtin.Nats
import P4SpecTec.Interface.Builtin.Numerics
import P4SpecTec.Interface.Builtin.Sets
import P4SpecTec.Interface.Builtin.Texts
import P4SpecTec.Interface.P4.Unparse
import P4SpecTec.Lang.Al.Ast
import P4SpecTec.Lang.Hints.Alter
import P4SpecTec.Lang.Hints.AlterJson
import P4SpecTec.Interp.InterpAl.Backtrack
import P4SpecTec.Interp.Effects
import P4SpecTec.Interp.InterpAl.Ctx
import P4SpecTec.Interp.InterpAl.Interp
import P4SpecTec.Lang.Al.Json
import P4SpecTec.Lang.Hints.Input
import P4SpecTec.Lang.Il.Ast
import P4SpecTec.Lang.Il.Json
import P4SpecTec.Lang.Xl.Bool
import P4SpecTec.Lang.Xl.Num
import P4SpecTec.Prelude
import P4SpecTec.Prelude.Eval
import P4SpecTec.Prelude.StateEval
import P4SpecTec.Prelude.Extern
import P4SpecTec.Prelude.Iter
import P4SpecTec.Prelude.Num
import P4SpecTec.Prelude.Value
import P4SpecTec.Refine.Calc
import P4SpecTec.Refine.Init
import P4SpecTec.Refine.StateCalc
import P4SpecTec.Refine.StateRules
import P4SpecTec.Refine.StateInterp
import P4SpecTec.Refine.StateNormalize
import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Value
import P4SpecTec.Runtime.Dynamic.Var
import P4SpecTec.Runtime.DynamicAl.Func
import P4SpecTec.Runtime.DynamicAl.Rel
import P4SpecTec.Runtime.Type.Equiv
import P4SpecTec.Runtime.Type.Expand
import P4SpecTec.Runtime.Type.Subst
import P4SpecTec.Runtime.Type.Typ
import P4SpecTec.Runtime.Type.Typdef
import P4SpecTec.Runtime.Value.Match
import P4SpecTec.Runtime.Value.Value
import P4SpecTec.Tactic.Audit
import P4SpecTec.Tactic.Det
import P4SpecTec.Tactic.Monotonicity
import P4SpecTec.Tactic.Refine
import P4SpecTec.Tactic.StateRefine
import P4SpecTec.Tactic.RunSound
import P4SpecTec.Tactic.StateRunSound
import P4SpecTec.Util.ByteText
import P4SpecTec.Util.Source
import P4SpecTec.Util.Yojson

/-!
# P4SpecTec

The core library: the deep embedding of P4-SpecTec's IL and AL
(`P4SpecTec.Lang.Il`, `P4SpecTec.Lang.Al`), its semantics ported from upstream's AL
interpreter (`P4SpecTec.Interp_al`, TRUSTED, with the runtime it needs under
`Runtime/` and `Interface/`), the runtime the generated code imports
(`P4SpecTec.Prelude`), the code generator (`P4SpecTec.Codegen`), and the
tactics that discharge generated theorems (`P4SpecTec.Tactic`).

Layout and principles: `docs/design.md`. A module whose path is an upstream
OCaml path, capitalised, mirrors that file (`Lang/Il/Ast.lean` mirrors
`lang/il/ast.ml`) under upstream's module name as its namespace, and says
so; `scripts/check-mirror.py` derives the pairs from the paths.
-/
