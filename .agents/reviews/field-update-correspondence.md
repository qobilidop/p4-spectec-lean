# Independent reverse-correspondence review

Reviewed 2026-09-25 by the state-codegen agent. Reviewed body:
`NanoP4Proofs/FieldUpdate/Correspondence.lean`, blob
`3de434b8218664a8ab62e617de1b02cdbdb58e20`.

## Ownership and verdict

No findings in the independently reviewed construction and assembly.

This reviewer authored the second-clause helpers, `thirdHead`,
`forwardSuccess`, and associated narrow normalization support during bounded
proof assistance. Those contributions are **not** claimed as independently
reviewed here. Root separately read and reviewed those contributions with no
findings. This report independently covers the props-owned dispatch, empty
case, first-clause rejection, recursive inequality/call/output/branch
assembly, raw-list termination induction, and final `alRealizesUpdate`
composition. The raw-shape inversion supplied by the oracle agent was also
read independently. No production-source edits were made during this review.

## Semantic checks

- Clauses are indexed out of the actual generated
  `NanoP4Spec.«$update_fieldValue».al` declaration; the helper does not replace
  it with handwritten alternative AL. The checked `invokeEq` equation
  retains ordered first/second/third attempts. The empty clause succeeds only
  on the empty list; on a nonempty input it rejects before subsequent clauses.
- `guard = false`, an empty local function environment, and the actual
  declaration's `Holds` contract are explicit operational assumptions.
  The exported theorem requires `HoldsSpec`, from which checked specification
  membership supplies this declaration contract. Internal/external entry and
  the recursive internal-call flag follow the interpreter equations.
- `thirdCall` passes the actual matched context, raw name, raw replacement,
  and the tail repackaged using the interpreter's exact list-note type. Its
  recursive invocation has fuel `fuel + 26`, compared with `fuel + 30` for
  third-clause evaluation and an additional three for enclosing dispatch.
- `rawRealizes` uses structural list induction at `7 * length + 33`.
  A nonmatching head consumes exactly seven units between whole invocations:
  the recursive tail call is at `7 * tail.length + 33`. The empty branch and
  matching-head branch use the already proved fixed-offset helper bounds.
  No termination hypothesis, duplicate-name restriction, or membership
  assumption on the requested name is introduced.
- Recursive contexts preserve the global table and have an empty local
  function environment by construction. Recursion occurs only on the actual
  tail; the input payload and key are not fabricated from generated values.
- Raw-shape inversion starts from `Rel` and recovers list/case/argument shape
  without equating raw notes or regions with canonical encodings. It proves
  only the shape needed for operational termination; payload semantics are
  established separately by checked forward refinement.
- The recursive result is destructed using its proved `ListV` shape with
  arbitrary result note and region. `thirdOutput` extracts the exact returned
  list and prepends the evaluated original head. It does not replace the
  recursive result with a presumed canonical encoding.
- `alRealizesUpdate` first obtains a real successful interpreter call, then
  applies the factored forward-success theorem at that exact fuel and output.
  The generated totality equality identifies the generated result. This
  closes the reverse direction rather than assuming successful evaluation.

The module correctly limits its claim to the helper on related inputs with
guards disabled. It does not prove arbitrary lvalue/assignment reordering,
expression effects, parsing, or surrounding whole-program behavior. Root's
later concrete-environment consumer wrappers are outside this frozen-body
review and require their own integration checks.

## Exact independent validation

Workdir: `/Users/qobilidop/my/work/p4-spectec-lean-field-update`.

```text
nix develop /Users/qobilidop/my/work/p4-spectec-lean --command \
  lake env lean NanoP4Proofs/FieldUpdate/Correspondence.lean
```

Actual exit 0, session 97664. The file hash was checked immediately before
and after re-elaboration and remained the reviewed blob. The exported
`alRealizesUpdate` exact `#guard_msgs` axiom check and `#audit_axioms` both
passed: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, added axiom,
native proof computation, kernel-check bypass or proof-budget increase was
used. The module's budgets match the imported generated refinement module.

Earlier diagnostic runs interrupted by the author were not successes.
The final factored proof above is the independently observed successful
revision. No full Lake build or full gate was run by this reviewer; final
library/root/consumer integration and publication gates remain root-owned.

## Root's complementary review

Root independently read the complete frozen operational body, including the
second-clause matching/false-guard calculations, reconstructed third-clause
head, normalization helpers and generic forward-success bridge authored by
the reviewer above. No findings: all clause expressions come from the actual
quotation, the unequal branch rejects before recursion, matching preserves
the raw tail, and the recursive output is consumed without re-encoding.
The generic forward bridge uses the existing checked refinement and generated
totality theorem; factoring it avoids expensive reduction at a computed fuel
without changing its statement or proof budgets.

After import additions and append-only closed wrappers, root's pinned
`lake build --wfail NanoP4Proofs` exited 0 (89 jobs, session 36932), including
the final consumer theorem and all exact axiom guards. The operational body
reviewed above was not edited. Closed wrappers and walkthrough receive the
separate consumer review.
