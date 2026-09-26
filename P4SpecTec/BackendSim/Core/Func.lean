import P4SpecTec.BackendSim.SpecImpl.Func
import P4SpecTec.BackendSim.SpecImpl.Unpack

/-!
Partial port of `p4spec/lib/backend-sim/core/func.ml`: verify only.
Both lookups precede Boolean unpacking, even when check is true or malformed.
Explicit callbacks preserve all outcomes and fresh post-state; context and
architecture values are returned unchanged. static_assert is not ported.
-/

namespace P4SpecTec.BackendSim.Core.Func

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude P4SpecTec.Util.Source
open P4SpecTec.BackendSim.SpecImpl

/-- Mirrors verify, including exact RETURN/REJECT shapes and distinct result notes. -/
def verify (call : SpecImpl.Func.Call) (value_ctx value_arch : value) :
    StateEval (value × value × value) := do
  let value_check ← SpecImpl.Func.find_var_e_local call value_ctx "check"
  let value_toSignal ← SpecImpl.Func.find_var_e_local call value_ctx "toSignal"
  let some check := Unpack.unpack_p4_bool value_check | throw .err
  let value_callResult := if check then
      let typ := .IterT (mkPhrase (.VarT (mkPhrase "value") [])) .Opt
      let value_eps := Value.Make.opt typ none
      Value.Make.case (.VarT (mkPhrase "returnResult") [])
        (.Seq [.Atom (mkPhrase (.Keyword "RETURN")), .Arg value_eps])
    else
      Value.Make.case (.VarT (mkPhrase "rejectResult") [])
        (.Seq [.Atom (mkPhrase (.Keyword "REJECT")), .Arg value_toSignal])
  pure (value_ctx, value_arch, value_callResult)

end P4SpecTec.BackendSim.Core.Func
