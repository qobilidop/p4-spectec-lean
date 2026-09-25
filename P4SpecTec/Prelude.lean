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

/-!
# P4SpecTec.Prelude

The runtime the generated code imports: values and their comparison, the
`ToValue` class, extern values, the meta-language's numerics, and the
ports of upstream's builtins under `Builtins/`, one module per OCaml file
of `p4spec/lib/interface/builtin/`.
-/
