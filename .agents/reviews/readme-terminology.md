# README terminology review

Independent read-only review, 2026-09-26. Documentation proposal against
implementation baseline `395022a`. No implementation edits or commits.

## Verdict

No blocking findings. The README is compact, describes the certification
goal, and immediately records partial Nano certification and incomplete
full-P4 support. Its principles concern technical choices. The current
example link names the existing directory; the proposed `ExampleProofs`
destination is explicitly future work in the note and handoff.

## Evidence and scope

- Read README, the full compiler-certification note, the documentation
  decision, AGENTS navigation and status handoff inside the Nix shell.
- Checked the generated refinement coverage header (18 of 153) and the
  field-update certificate's source, initialization, representation and
  bidirectional correspondence fields. The note distinguishes this bounded
  handwritten certificate from generated one-direction coverage.
- Independently read SpecTec PLDI 2024 section 6 and the official March 2025
  adoption update. The note correctly separates Wasm soundness proofs from
  proofs of translation, and dates the backend milestone.
- Read K CAV 2021 sections 4 and 7.2: execution proof objects use matching
  logic in Metamath; K-to-Kore compilation and domain reasoning remain
  trusted in that implementation. The note accurately limits its comparison.
- Read Skel CPP 2022 sections 2.4 and 3 and its stated contributions:
  generic abstract-machine soundness against the concrete interpretation,
  instantiated on generated deep syntax, differs from per-definition
  translation certificates. The note preserves that distinction.
- Cogent, AutoCorres, CakeML, Alive2 and Trivet claims are outside this
  reviewer's independently researched source scope; they rely on the
  separate primary-source research supplied to the authoring agent.

No Lean builds or full gate were rerun for this documentation-only review.
The main agent handles documentation hygiene. User review remains required
before committing, publishing or resuming the approved refactor.

## Rationale follow-up

Reviewed the README's revised certification principle, the note's new
"Why this choice fits the project" section and the matching status addition.
No findings. Checking a reusable language model at build time accurately
distinguishes this artifact from compilation of individual P4 programs.
Generator flexibility is a concrete architectural rationale; the note
correctly retains source-identity and statement-adequacy obligations, partial
coverage, checking costs and unestablished full-P4 scalability. It claims no
universal advantage over compiler verification. No implementation change,
commit or further refactor is implied.

## Dedicated Rationale section follow-up

Independently reviewed the final README wording and matching note/status
updates after the user's approval. No findings. Per-definition correctness
proofs are explicitly a goal, partial certification remains visible, and
model reuse is accurately distinguished from per-program certification.
The shortened correspondence principle agrees with the rationale.
