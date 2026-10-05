import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
The axiom audit of generated theorems: `#audit_axioms name ...` fails unless
every axiom the named theorems depend on is one of `propext`,
`Classical.choice` and `Quot.sound` (the three `partial_fixpoint` and
`simp` introduce). A `sorry`, a `native_decide` (`Lean.ofReduceBool`) or
any other axiom fails the build, which is the audit design section 5
(rung 1) asks for; the exact set is not named because it differs
between theorems and the generator does not compute it. With several names
the failure reports the axioms, not which theorem reaches them.
-/

namespace P4SpecTec.Tactic

open Lean Elab Command

/-- The axioms a generated theorem may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms the named declarations depend on, with every declaration of the current
module visited once for all of them. `Lean.collectAxioms` starts afresh for each name, so
auditing the fifty theorems projected from one joint proof traversed that proof fifty
times. Imported declarations use Lean's own collection, which is precomputed. As Lean
does, constants are read from the kernel environment: a theorem whose proof failed in a
task is an axiom there. -/
partial def sharedAxioms (names : Array Name) : CommandElabM NameSet := do
  let env ← getEnv
  let kernel := env.checked.get
  let rec visit (c : Name) : StateT (NameSet × NameSet) CommandElabM Unit := do
    if (← get).1.contains c then return
    modify fun (seen, found) => (seen.insert c, found)
    if (env.getModuleIdxFor? c).isSome then
      let imported ← collectAxioms c
      modify fun (seen, found) => (seen, imported.foldl (·.insert ·) found)
    else
      let expr (e : Expr) : StateT (NameSet × NameSet) CommandElabM Unit :=
        e.getUsedConstants.forM visit
      match kernel.find? c with
      | some (.axiomInfo v) =>
        modify fun (seen, found) => (seen, found.insert c)
        expr v.type
      | some (.defnInfo v) => expr v.type *> expr v.value
      | some (.thmInfo v) => expr v.type *> expr v.value
      | some (.opaqueInfo v) => expr v.type *> expr v.value
      | some (.quotInfo _) => pure ()
      | some (.ctorInfo v) => expr v.type
      | some (.recInfo v) => expr v.type
      | some (.inductInfo v) => expr v.type *> v.ctors.forM visit
      | none => pure ()
  let (_, (_, found)) ← (names.forM visit).run ({}, {})
  pure found

/-- Fail unless the named declarations depend only on the allowed axioms. -/
elab "#audit_axioms " ids:ident+ : command => do
  let names ← ids.mapM fun id => liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
  let axioms ← sharedAxioms names
  let bad := axioms.toList.filter fun a => !allowedAxioms.contains a
  unless bad.isEmpty do
    let subject := if h : names.size = 1 then m!"{names[0]}" else m!"{names.toList}"
    throwError "{subject} depends on axioms outside the allowed set: {bad}"

end P4SpecTec.Tactic
