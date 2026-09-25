import P4SpecTec.Runtime.Value.Value
import P4SpecTec.Interface.P4.Unparse
import P4SpecTec.Interface.Builtin.Texts
import P4SpecTec.Interface.Builtin.Lists
import P4SpecTec.Interface.Builtin.Sets
import P4SpecTec.Interface.Builtin.Maps
import P4SpecTec.Interface.Builtin.Nats
import P4SpecTec.Interface.Builtin.Ints
import P4SpecTec.Interface.Builtin.Numerics
import P4SpecTec.Prelude.Value
import P4SpecTec.Prelude.Eval
import P4SpecTec.Prelude.Extern
import P4SpecTec.Prelude.Num
import P4SpecTec.Prelude.Iter

/-!
# P4SpecTec.Prelude

The runtime the generated code imports: the mirrored value operations
(`Runtime.Value`), the mirrored printer (`P4.Unparse`) and
builtins (`Builtin.*`), and our own `ToValue`/`OfValue` classes, the
`Eval` monad, extern values, numerics and iteration helpers under `Prelude/`.
-/
