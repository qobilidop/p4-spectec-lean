# Certification rationale and open questions

Durable discussion reference and paused design questions, compacted 2026-09-26.
The user requested preservation of this discussion. This is not a second
literature survey or authorization for new implementation.

## Settled direction and where it lives

[README](../../README.md) owns concise motivation and rationale,
[Design](../../docs/design.md) the intended contract, and
[Related Work](../../docs/related-work.md) the primary-source synthesis.
[Certification](../../docs/certification.md) owns delivered guarantees.

The project translates a language specification, not P4 programs to machine
code. Keeping pace with the evolving specification and providing a reference
for alternative Lean models are the user benefits. Checking translations is
our responsibility supporting those benefits, not a separate project purpose.

“Certifying compiler” names the goal; “proof-producing semantics translation”
describes the mechanism. The choice favors an evolving generator and reusable
language models whose proofs are checked once per model build. It is not a
claim of superiority over verified compilers, a universal generator theorem,
or certification of Lean's native backend. Checking costs and full-P4 scale
remain real obligations. Certified, verified and certifying are overlapping
architectures, not a rigid hierarchy.

The closest specific architectural comparisons are Cogent's deep-to-shallow
phase and AutoCorres. CakeML's proof-producing translator has the opposite
translation direction; its verified machine-code backend is separate.
Wasm SpecTec is closest in purpose; generated-model metatheory is different
from translation correspondence. Primary sources and their guarantee limits
are maintained in Related Work rather than copied here.

## Open judgments from the design review

The independent critique reviewed baseline
`c215d102758c00b829a50085e1e271185a176613` on 2026-09-25.
Its approved first consumer milestone is now complete
([field-update evidence](field-update.md)); broader M3 remains paused.
Remaining proposals are advisory:

- Make certification coverage machine-readable by source identity, definitions,
  dependencies, theorem names, representations, environments and exclusions.
  A strict entry-point certificate needs every reachable contract. Successful
  generation is distinct from successful certification.
- Generalize source representation adequacy beyond the completed scalar case.
  Validity, coverage and decoding do not follow from canonical equality alone;
  printing, callbacks and metadata need observation-specific contracts.
- Expand distinguishing mutations: alternative order, hard-error retry, state
  reset after rejection, omitted constructors, wrong quotations, jointly
  altered executable/relation, and print provenance. Identify which boundary
  rejects each defect rather than claiming all layers detect it.
- Measure maintenance across actual upstream changes: manual repair to the
  reference, generator, certificates, API and consumer proofs. Record effort
  and cause, not only generated counts.
- Let consumer evidence justify stable wrappers and reusable semantic lemmas.
  A proved adapter is not a failure of generation. Preserve provenance without
  assuming every generated name is a permanent ergonomic client API.
- Profile generation, elaboration, proof checking, memory and incremental
  rebuilds separately. Historical group durations are not current benchmarks.

AL, the reference interpreter and the generated model remain the chosen
architecture. An IL backend or interpreter-only redesign requires a concrete
consumer problem and newly agreed scope. Kernel validity cannot establish
statement adequacy or source fidelity by itself; determinism cannot replace
a finite reverse witness. No novelty claim follows merely from using Lean.

## Historical evidence

Full discussion and advisory review are available at `968ad65` in
`compiler-certification.md` and `design-review.md` under `.agents/notes/`.
The 2026-09-26 README review independently checked SpecTec, K and Skel;
separate related-work reviewers checked P4 comparisons and Cogent/AutoCorres/
CakeML/Sail. The HOL4P4 ACM full-paper fetch was unavailable, so the comparison
used the primary conference record without invented section numbers. Cogent
2016 was corrected to an arXiv preprint, not attributed to another paper's venue.
These were documentation/source reviews, not fresh Lean proof or scale audits.
All detailed reviewer limitations remain in the corresponding historical
README/related-work/project-state documentation reports at that commit.
