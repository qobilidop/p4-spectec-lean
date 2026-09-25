import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
The axiom audit of generated theorems: `#audit_axioms name` fails unless
every axiom the theorem depends on is one of `propext`,
`Classical.choice` and `Quot.sound` (the three `partial_fixpoint` and
`simp` introduce). A `sorry`, a `native_decide` (`Lean.ofReduceBool`) or
any other axiom fails the build, which is the audit design section 5
(rung 1) asks for; the exact set is not named because it differs
between theorems and the generator does not compute it.
-/

namespace P4SpecTec.Tactic

open Lean Elab Command

/-- The axioms a generated theorem may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Fail unless the named declaration depends only on the allowed axioms. -/
elab "#audit_axioms " id:ident : command => do
  let names ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
  let axioms ← collectAxioms names
  let bad := axioms.filter fun a => !allowedAxioms.contains a
  unless bad.isEmpty do
    throwError "{names} depends on axioms outside the allowed set: {bad.toList}"

end P4SpecTec.Tactic
