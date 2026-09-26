# Field-update consumer evidence

Completed bounded example; retained evidence and limits, compacted 2026-09-26.
The maintained proof, walkthrough and tests live together in
[ExampleProofs/NanoP4FieldUpdate](../../ExampleProofs/NanoP4FieldUpdate/).
[Certification](../../docs/certification.md) owns the user-facing guarantee.

## Contract and maintenance constraints

The certificate connects the actual generated update helper and its quoted
AL reference in both directions on an independently selected scalar source
domain. Initialization, dependency lookup, representation coverage and finite
reference witnesses are discharged. Sequential reference calls feed the first
actual raw result into the second, not a substituted generated encoding.

The source profile permits finite ordered lists, duplicates, absent keys,
arbitrary byte names, natural widths and arbitrary Int payloads for the
selected W/S, Boolean and match-kind constructors. It does not claim all AL
numeric encodings, source parsing, type/range validity, nested/extern payloads,
printing, or arbitrary P4 assignment reordering. Generated update laws have
a wider value domain than the source correspondence claim.

First-match update preserves the remaining suffix and returns the original
list for an absent name. Distinct-name commutation needs neither uniqueness
nor field presence. Replacement values are already evaluated. Reverse
realization supplies a finite witness (`7 * length + 33` for the raw-list
construction), not success at every fuel; fuel exhaustion is not semantic
error or evidence of divergence. The scalar/field decoder bounds `fuel + 5`
and `fuel + 6` concern explicit encodings, not every annotated representative.

Mutation sensitivity is bounded artifact testing, not general generator
mutation coverage. Baseline success precedes mutant acceptance. Behavior
fails at `update_fieldValue.refines_group`, quotation at `compareSpecs`,
and representation at `Scalar.sourceRel`. Unexpected diagnostics, stale
reports, missing mutations, warnings and timeouts fail the harness.

Runtime probes have 60-second deadlines; proof replay has 300 seconds with
the unchanged 4M heartbeat ceiling. The original uniform 60-second deadline
failed CI run `36260016481`; the repair passed at `395022a`, run
`36261314804`. Raising process time did not weaken proof obligations.

## Independent review provenance

The 2026-09-25/26 reports are recoverable at commit `968ad65` under the
former `.agents/reviews/field-update-*.md` paths. They are historical
AI-agent reviews, not new audits performed during compaction.

- State-codegen agent reviewed Domain/Representation and directly re-elaborated
  the latter. Root independently reviewed the oracle-authored Environment.
- Oracle agent reviewed Semantics/Laws and consumer additions. It did not
  independently review its own Environment or raw-shape assistance.
- State-codegen agent reviewed the reverse dispatch/induction assembly, frozen
  Correspondence blob `3de434b8218664a8ab62e617de1b02cdbdb58e20`.
  Root separately reviewed that agent's matching/normalization helpers.
  The actual direct Lean check exited 0; interrupted diagnostics were not passes.
- Final consumer review used Correspondence SHA-256
  `9a3c45fa685396dc9fcf310cf868e743bc87e815e11122756d7ead105544560f`
  and Example SHA-256
  `d010cad2757984bbe61e2c5171c8b4ecd2317f022f7b61a2c543d464890d55fa`.
  Both direct Lean elaborations passed with exact core-three axiom audits.
- PR #27 merged as `a492c60`, retaining implementation `4612534`;
  run `36224020037` succeeded on that head. Later certificate packaging was
  independently reviewed by `/root/p4_oracle`, including direct Init,
  Certificate and Example checks and all intended mutation boundaries.
- Independent timeout review ran all nine runner contracts and the real
  mutation suite successfully. An overlapping author's missing-artifact failure
  was correctly rejected rather than counted as a mutant rejection.

## Library separation

Commit `aa24ab7` renamed the example from NanoP4Proofs without a compatibility
shim. All ten moved proof/test files were mechanically identical except
names/paths; the root comment additionally explains its consumer role.
Examples are excluded from default targets but explicitly built by the gate.
Reusable proof support remains in `P4SpecTec.Refine`.

Independent `doc_guides_review` found a package-level srcDir inventory gap
in the parser-backed boundary checker. It was fixed with a regression; all
27 policy/parser tests and the actual checker passed independently. Root's
default build (139 jobs), example build (91), nine runner contracts and full
gate passed. Remote run `36268161537` subsequently completed successfully
on `aa24ab7`, verified during this maintenance pass. This closes that
publication obligation, not broader M3. Historical detail is in the
`example-library.md` review at `968ad65`.
