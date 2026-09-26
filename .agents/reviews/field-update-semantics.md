# Field-update semantics and laws review

Independent read-only review by the oracle agent, 2026-09-25. The reviewer
authored the separate `Environment` module, not the three modules reviewed
here. Only this report was written during the review.

## Scope and frozen identities

Reviewed `NanoP4Proofs/FieldUpdate/Semantics.lean`, `Laws.lean`, and the current
`Example.lean`, against the actual generated helper in
`NanoP4Spec/8.04-eval-lvalue.lean` and pinned source
`upstream/nano-p4-spec/8.04-eval-lvalue.watsup`, lines 7–22. Representation
definitions were read to check the scalar bridge's meaning.

SHA-256 at review:

- Semantics: `9284dcfe23c286f030e732c2a996467b0bada85eaab2d9a992255c053b5274a6`
- Laws: `0cc07542e1d326ea413a16e506c5b1af116ef0a7e7c92e10829986472a8a16ff`
- Example: `c3c8b1ed60a2bfd883f36a5bc3cbb475dcba93154ed4efa362dd521fd08fd82e`

## Findings

No findings in this bounded scope.

`generatedEqUpdate` proves successful termination and equality for the actual
generated partial-fixpoint operation, rather than merely assuming an interface
semantics. Its induction follows the empty, matching-head, and nonmatching-head
branches of the generated operation. Name comparison is proved equivalent to
exact byte-string equality, without text normalization.

The first-match laws preserve order and duplicate multiplicity, leave the
entire suffix after the first match unchanged, and return the original list
when the name is absent. Distinct-name commutation is valid without uniqueness
or occurrence assumptions. `generatedCommute` concerns two actual generated
computations, including their successful outcome, with already evaluated
replacement values. It makes no claim that effectful expressions or arbitrary
P4 assignments commute.

There are two deliberately different domains. The generated totality and laws
quantify over every generated `fieldValue` and `value`, including nonscalar
payloads. `generatedFieldsUpdate` and the current consumer example instantiate
them with the independently selected scalar source profile: finite ordered
lists, arbitrary byte names, W/S integer-literal shapes, booleans, and match
kinds. No invented width/payload range, name validity, uniqueness, or
field-presence premise narrows that profile. This broader generated-domain law
does not itself establish source-interpreter correspondence for arbitrary
nested/extern values. The current Example proves generated-operation
commutation only; reverse interpreter realization and closed reference
transfer are separate obligations being implemented elsewhere.

Every advertised theorem in the reviewed modules has an exact checked axiom
listing of `propext`, `Classical.choice`, and `Quot.sound`. No `native_decide`,
new axiom, `sorry`, or conditional termination premise was introduced.

## Independent validation

Inside the pinned Lean Nix shell, with working directory
`/Users/qobilidop/my/work/p4-spectec-lean-field-update`, ran each command directly:

```text
lake env lean /Users/qobilidop/my/work/p4-spectec-lean-field-update/NanoP4Proofs/FieldUpdate/Semantics.lean
lake env lean /Users/qobilidop/my/work/p4-spectec-lean-field-update/NanoP4Proofs/FieldUpdate/Laws.lean
lake env lean /Users/qobilidop/my/work/p4-spectec-lean-field-update/NanoP4Proofs/FieldUpdate/Example.lean
```

Actual exits were respectively 0, 0, 0 (0.502 s, 0.409 s, 0.347 s). Each exact
axiom-message check passed. Root's prior focused library build was not
duplicated. No full gate or publication claim is made by this review.

## Forward reference consumer follow-up

Independently reviewed the subsequent root-authored reference section in
`Example.lean`: `referenceUpdate`, `referenceWrites`, `ReferenceObserves`,
`referenceSound`, `referenceWritesSound`, and `referenceObservationSound`.
The reviewed Example SHA-256 is
`67e747f6640827dded6999e527821044e7fc107acd388206a514c59b0f6e5fc2`.
No source changes were made by the reviewer.

No findings. `referenceUpdate` invokes the actual quoted helper in the concrete
initialized `Environment.ctx`, with guard/debug disabled. The refinement
theorem's guard, local function environment, complete specification, and
callee obligations are discharged from actual constants/proofs; they are not
extra hypotheses of the public consumer theorem. Related raw input values
remain arbitrary, including their notes and regions.

The sequential definition feeds the actual first returned raw value directly
to the second interpreter invocation. The proof splits the first invocation's
actual outcome, establishes its successful related intermediate value, and
uses that relation as the second invocation's input premise. It does not feed
a generated encoding or an assumed intermediate value into the reference
execution.

These are forward-only results. A defined reference outcome is proved
successful and related to the corresponding generated update. An observed
successful two-call output has the unique stated canonical observation.
Existentially hiding the two fuel budgets does not assert that either budget
exists for every input, that arbitrary finite budgets terminate, or that `none`
is a semantic error. Closed observation existence, reverse realization, and
reference commutation remain separate obligations pending the reverse proof.

Reran the direct pinned-Nix command
`lake env lean /Users/qobilidop/my/work/p4-spectec-lean-field-update/NanoP4Proofs/FieldUpdate/Example.lean`
from the field-update worktree; actual exit 0, including the three new exact
core-three axiom checks. No Lake build, full gate, or publication was performed
for this follow-up review.
