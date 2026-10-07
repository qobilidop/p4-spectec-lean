import P4SpecTec.BackendSim.SpecImpl.Func
import P4SpecTec.BackendSim.SpecImpl.Unpack

/-!
Partial port of `p4spec/lib/backend-sim/core/func.ml`: verify and static_assert.
Lookups precede Boolean unpacking, even when check is true or malformed.
Explicit callbacks preserve all outcomes and any carrier state; context and
architecture values are returned unchanged. A failed static_assert is a hard error, as
upstream's target abort is (one p4c error test exercises it on both legs):
`Fail` carries no message, so the message is looked up, as upstream does before testing
the check, but not unpacked.
-/

namespace P4SpecTec.BackendSim.Core.Func

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude P4SpecTec.Util.Source
open P4SpecTec.BackendSim.SpecImpl

/-- Mirrors verify, including exact RETURN/REJECT shapes and distinct result notes. -/
def verify {m : Type → Type} [Monad m] [MonadExceptOf Fail m] (call : SpecImpl.Func.Call m)
    (value_ctx value_arch : value) : m (value × value × value) := do
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

/-- Mirrors static_assert: the checked value itself when it is true, an error otherwise.
With `message`, the message lookup runs before the check is unpacked. -/
def static_assert {m : Type → Type} [Monad m] [MonadExceptOf Fail m]
    (call : SpecImpl.Func.Call m) (message : Bool) (value_ctx : value) : m value := do
  let value_check ← SpecImpl.Func.find_var_value_t_local call value_ctx "check"
  if message then
    let _ ← SpecImpl.Func.find_var_value_t_local call value_ctx "message"
  let some check := Unpack.unpack_p4_bool value_check | throw .err
  if check then pure value_check else throw .err

end P4SpecTec.BackendSim.Core.Func
