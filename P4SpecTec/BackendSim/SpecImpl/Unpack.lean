import P4SpecTec.Runtime.Value.Value

/-!
Partial port of `p4spec/lib/backend-sim/spec_impl/unpack.ml`: only unpack_p4_bool.
An optional result replaces raising runtime getters; callers map failure to
a hard error. Other P4 unpackers and argument pairing are not ported.
-/

namespace P4SpecTec.BackendSim.SpecImpl.Unpack

open P4SpecTec.Lang.Il P4SpecTec.Runtime

/-- Require exactly the pinned `_B bool` mixop followed by a Boolean payload. -/
def unpack_p4_bool (v : value) : Option Bool := do
  let .CaseV (.Seq [.Atom a, .Arg b]) := v.it | none
  unless a.it == .Tag "B" do none
  Value.Get.bool b

end P4SpecTec.BackendSim.SpecImpl.Unpack
