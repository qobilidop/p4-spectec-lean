# Final field-update consumer review

Independent read-only review by the oracle agent, 2026-09-25. Reviewed the
entire final `Example.lean` and the public reference APIs in
`Correspondence.lean`, especially additions after `alRealizesUpdate`.
The reviewer authored `Environment` and the delegated raw-shape scratch
lemma, not these consumer additions. The operational reverse-proof body has
the separate complementary review; this report does not replace it.
Only this report was written during the review.

## Frozen source and result

Reviewed SHA-256:

- Correspondence: `9a3c45fa685396dc9fcf310cf868e743bc87e815e11122756d7ead105544560f`
- Example: `d010cad2757984bbe61e2c5171c8b4ecd2317f022f7b61a2c543d464890d55fa`

No findings in this bounded consumer scope.

`referenceRealizes` specializes the actual quoted-helper realization theorem
to the concrete initialized context. Guard configuration, successful
initialization, local function environment, complete-specification/callee
lookup, and finite-fuel existence are discharged, not left as public
assumptions. The remaining `Rel` premises express the input representation.
They allow arbitrary raw source notes and regions.

`referenceWritesRealize` first obtains an actual successful raw result, then
passes that same raw value to the second invocation. Its proven representation
relation—not an encoder round trip or assumed intermediate value—supplies the
second realization premise. Both finite budgets are constructed by the
realization theorem. The matching forward sequence theorem follows exactly
the same actual raw data flow.

`referenceObservesIff` characterizes successful observable reference outcomes
in both directions. Its reverse direction constructs the two actual successful
runs and uses the resulting relation to establish the stated observation;
it does not assume termination or a successful result. The forward direction
uses the already reviewed all-defined-outcome soundness result, which also
rules out terminating errors on related inputs. No theorem claims success at
every fuel budget or identifies finite-fuel `none` with semantic failure.
The observation predicate existentially hides the two resource budgets; it
does not assert equality of the execution traces or fixed-budget runs.

`referenceWritesExist` covers every independently declared `SourceFields`
input through representation coverage, without requiring it to be literally
the generated encoder's output. `independentReferenceWritesCommute` transfers
the generated first-match commutation law to the actual reference observations.
Its only behavioral side condition is distinct names. The scalar source domain
still permits empty lists, absent keys, duplicate names, arbitrary exact byte
names, natural widths and arbitrary integer payloads. It introduces no range,
typing, uniqueness, field-presence, environment or termination condition.

The walkthrough's limits are accurate: replacement scalar values are already
evaluated, and the theorem does not commute arbitrary P4 assignments or lvalue
evaluation effects. Nested/extern payloads, packet/table objects, printing and
source parsing are outside this source-level consumer profile, even though
the general generated update laws quantify over all generated values.

Trust documentation correctly distinguishes Lean kernel-checked generated
semantics/reference proofs from the empirical quotation/export boundary.
The 342-definition quotation check connects the quoted syntax to the pinned
export; it does not prove the exporter/parser or the OCaml-to-Lean port.
No fresh-state, complete-program, whole-corpus or full-P4 claim is added.

## Independent validation

After root's focused library build completed, directly elaborated both files
in the pinned Lean Nix shell, using the field-update worktree as working
directory:

```text
lake env lean /Users/qobilidop/my/work/p4-spectec-lean-field-update/NanoP4Proofs/FieldUpdate/Correspondence.lean
lake env lean /Users/qobilidop/my/work/p4-spectec-lean-field-update/NanoP4Proofs/FieldUpdate/Example.lean
```

Actual exits: 0 and 0; elapsed 6.569 s and 0.419 s. Exact axiom checks passed,
with only `propext`, `Classical.choice`, and `Quot.sound`. No new axiom,
`native_decide`, `sorry`, or proof assumption bypass was used. No concurrent
Lake build or full gate was run by this reviewer. Final full gate and
publication remain root's separate obligations.
