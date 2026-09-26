import NanoP4Spec.Refinement.Spec
import P4SpecTec.Refine.Init

/-!
A concrete initialized environment for the quoted Nano-P4 specification.
Logical hash-map laws, rather than reduction of opaque string hashing, prove
that initialization succeeds. Only finite definition names are computed.
This module is our own consumer support, not an upstream mirror.
-/

namespace ExampleProofs.NanoP4FieldUpdate.Environment

-- Match the quoted specification's existing proof budgets for its deep list.
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open P4SpecTec
open P4SpecTec.Interp_al

private theorem nanoKeysUnique : Refine.Init.NamesUnique NanoP4Spec.spec := by decide

/-- The concrete global tables built from every quoted Nano-P4 definition. -/
def global : Ctx.global := Refine.Init.global NanoP4Spec.spec

/-- Actual Nano-P4 initialization succeeds and yields the concrete tables. -/
theorem initEqOk : Ctx.init NanoP4Spec.spec = .ok global :=
  Refine.Init.initEqOk _ nanoKeysUnique

/-- info: 'ExampleProofs.NanoP4FieldUpdate.Environment.initEqOk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms initEqOk
#audit_axioms initEqOk

/-- The concrete environment holds the entire quoted specification. -/
theorem holdsSpec : Refine.HoldsSpec NanoP4Spec.spec global :=
  Refine.holdsSpec_of_init initEqOk

/-- info: 'ExampleProofs.NanoP4FieldUpdate.Environment.holdsSpec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms holdsSpec
#audit_axioms holdsSpec

/-- A concrete interpreter context with no local bindings. -/
def ctx : Ctx.t := Ctx.empty global

/-- The initialized consumer context has no local function overrides. -/
theorem localFenvEmpty : ctx.local.fenv = [] := rfl

/-- info: 'ExampleProofs.NanoP4FieldUpdate.Environment.localFenvEmpty' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms localFenvEmpty
#audit_axioms localFenvEmpty

end ExampleProofs.NanoP4FieldUpdate.Environment
