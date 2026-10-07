import P4SpecTec.BackendSim.SpecImpl.Func
import P4SpecTec.BackendSim.SpecImpl.Rel

/-!
Partial port of `p4spec/lib/backend-sim/make.ml`: only the failure behavior of the
registered trampolines, `call_func` composed with the interpreter's `eval_func` and
`call_rel` composed with its `eval_rel`. Mode dispatch, the program trampoline, STF
handling and simulator state are not ported here; the STF statement runner is in
`BackendSim/Stf/`.

Upstream `eval_func` and `eval_rel` return both AL failure kinds (`Err`, `Unmatch`) as
`Fail (Unmatch _)`; the trampolines raise it as `ExternError`, and the target's
`Extern.eval_extern_rel` returns it as a failure that `invoke_extern_rel` treats as a
mismatch. A failed callback therefore makes the whole extern call a retryable mismatch,
whichever kind the callee produced. The Lean `Fail` does not separate a nested target abort
from AL `Err`, so a callback whose closure reaches an extern would also collapse such an
abort. NanoSwitch registers only callbacks whose closures reach no extern (`find_var_e`,
`write_value_from_bits`, `update_var_e`), and the placeholder target only
`find_var_value_t`, which reaches none either; v1model's callbacks are the storage,
type and table functions and the `Lvalue_read`/`Lvalue_write` relations, none of which
reaches an extern.
-/

namespace P4SpecTec.BackendSim.Make

open P4SpecTec.Prelude

/-- Mirrors `call_func` around `eval_func`: success passes through; either failure kind of
the callee becomes a mismatch, retaining any carrier state (a fresh counter) at failure. -/
def call_func {m : Type → Type} [Monad m] [MonadExceptOf Fail m]
    (call : SpecImpl.Func.Call m) : SpecImpl.Func.Call m :=
  fun name typs values => tryCatch (call name typs values) fun _ => throw .unmatch

/-- Mirrors `call_rel` around `eval_rel`, with the same failure collapse. -/
def call_rel {m : Type → Type} [Monad m] [MonadExceptOf Fail m]
    (call : SpecImpl.Rel.RelCall m) : SpecImpl.Rel.RelCall m :=
  fun name values => tryCatch (call name values) fun _ => throw .unmatch

/-- The registered trampolines a target's extern code calls back through: mirrors the
`Spec.S` argument of upstream's architecture functors. -/
structure Spec (m : Type → Type) where
  /-- `Spec.Func.call`. -/
  func : SpecImpl.Func.Call m
  /-- `Spec.Rel.call`. -/
  rel : SpecImpl.Rel.RelCall m

end P4SpecTec.BackendSim.Make
