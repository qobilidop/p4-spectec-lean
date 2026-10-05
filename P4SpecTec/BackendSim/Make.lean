import P4SpecTec.BackendSim.SpecImpl.Func

/-!
Partial port of `p4spec/lib/backend-sim/make.ml`: only the failure behavior of the
registered function trampoline, `call_func`, composed with the interpreter's `eval_func`.
Mode dispatch, relation/program trampolines, STF handling and simulator state are not ported.

Upstream `eval_func` returns both AL failure kinds (`Err`, `Unmatch`) as `Fail (Unmatch _)`;
`call_func` raises it as `ExternError`, and the target's `Extern.eval_extern_rel` returns it
as a failure that `invoke_extern_rel` treats as a mismatch. A failed callback therefore makes
the whole extern call a retryable mismatch, whichever kind the callee produced. The Lean
`Fail` does not separate a nested target abort from AL `Err`, so a callback whose closure
reaches an extern would also collapse such an abort. NanoSwitch registers only callbacks
whose closures reach no extern (`find_var_e`, `write_value_from_bits`, `update_var_e`), and
the placeholder target only `find_var_value_t`, which reaches none either.
-/

namespace P4SpecTec.BackendSim.Make

open P4SpecTec.Prelude

/-- Mirrors `call_func` around `eval_func`: success passes through; either failure kind of
the callee becomes a mismatch, retaining any carrier state (a fresh counter) at failure. -/
def call_func {m : Type → Type} [Monad m] [MonadExceptOf Fail m]
    (call : SpecImpl.Func.Call m) : SpecImpl.Func.Call m :=
  fun name typs values => tryCatch (call name typs values) fun _ => throw .unmatch

end P4SpecTec.BackendSim.Make
