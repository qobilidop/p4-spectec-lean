# Compiler certification: terminology and closest prior art

Discussion reference, 2026-09-26. Implementation baseline: `395022a`.
The user approved the README and related-work revision. This note records the reasoning
behind its terminology; it does not authorize new implementation work.
Its literature synthesis is incorporated into `docs/related-work.md`, identifying
Cogent's deep-to-shallow phase and AutoCorres as close architectural precedents.

## Agreed positioning

Describe the goal as a **certifying compiler** from P4-SpecTec's algorithmic
language (AL) to executable definitions and inductive relations in Lean 4.
Use **proof-producing semantics translation with per-definition correspondence
certificates** when a more technical description is useful.

Keep the opening goal-focused. Use the README's Status section to distinguish
current coverage from that goal. Do not call Nano-P4 fully supported merely
because its generated specification builds. The proposed title,
**P4-SpecTec to Lean 4**, makes the translation direction explicit without
putting specialized certification terminology in the title.

The motivation has two parts: follow an evolving specification through
P4-SpecTec, and provide a reference against which alternative, more
proof-friendly Lean models can establish agreement. Translation checking is
an engineering responsibility supporting those goals, not a separate reason
for users to want the project. The README's dedicated Rationale section
separates project motivation from the justification for per-translation
certification. Its heading is "Why a certifying compiler?", avoiding a false
opposition between certifying and certified. Design principles retain the
short implementation rule: check correspondence, not just compilation.

Design principles should guide technical choices between plausible solutions.
Mirroring the reference rather than independently redesigning it, and proving
individual translations rather than the generator itself, meet that test.
Library/example separation is repository organization guidance, not a README
design principle. It remains an approved refactor, not part of this edit.

## What is being translated and proved?

The input is a specification of P4 semantics, represented as AL syntax.
The output is a model of those semantics in Lean, not machine code for an
individual P4 program. A deep embedding represents AL syntax as data with an
explicit interpreter; a shallow embedding represents operations as ordinary
Lean definitions. The generated relations are an additional logical interface.

The generator emits definitions and proof scripts. Lean reconstructs and
checks proofs for the supported fragment. This is not a universal proof of
the generator implementation, and it does not certify Lean's native compiler.

The intended executable contract is agreement on terminating observable
behavior in both directions, for a declared supported domain. Representation,
environment, failure and relevant state obligations are part of that contract.
A generated relation's run-soundness theorem is a different guarantee; it
does not automatically establish exact correspondence with execution.

At this baseline, generated AL refinement covers 18 of 153 Nano definitions
in one direction (`NanoP4Spec/Refinement.lean`). The handwritten field-update
example supplies both directions on its scalar domain, including concrete
initialization and representation obligations. General reverse realization
and full-P4 coverage remain incomplete.

The proof boundary starts at the formalized AL reference. Upstream parsing,
elaboration and algorithmization remain outside that proof. Independent
quotation comparison checks the external export against the quoted input;
it is a runtime check, not a kernel theorem about the external file. A valid
proof about the wrong quotation or an accidentally narrowed domain would not
establish the intended source claim. See `docs/design.md`, sections 5–5.2.

## Terminology

Leroy's POPL 2006 paper, section 2, separates a compiler-level correctness
theorem from generating evidence for individual translations. It also shows
how a sound validator combined with an untrusted generator can yield a
certified compiler. These are overlapping architectures, not a rigid ranking.
Producing proof scripts or reconstruction hints rather than complete proof
terms is compatible with certifying compilation.
[Leroy, Formal Certification of a Compiler Back-end, §2][leroy]

| Term | Recommended use here |
|---|---|
| Verified compiler | Avoid as the headline: suggests a compiler-level theorem, which can combine verified transformations and validators. |
| Certified compiler | Ambiguous about the mechanism and coverage. |
| Certifying compiler | Preferred public goal: translation produces independently checkable evidence. |
| Proof-producing translator | Preferred technical description: construct and check translation-specific proofs. |
| Translation validation | Per-translation checking rather than a universal generator proof; not differential testing. |

Being written in Lean does not make the generator verified. Conversely, an
unverified generator does not prevent trustworthy output when the required
theorem is checked. The statement and source connection still need scrutiny.

## Why this choice fits the project

This is a project-specific justification, not a claim that certifying
compilation is generally better than compiler verification:

- We generate a language model that many downstream programs and proofs can
  use. Certification is paid for when building that model, not repeated for
  each P4 program or packet.
- The generator must evolve with AL coverage and the Lean interface. Checking
  translation-specific proofs lets that implementation change without relying
  on its correctness. A failed proof blocks certification of the affected
  artifact; generating uncertified definitions is not certification.
- The emitted definitions and proofs are checked together. This fits the
  existing text-generation workflow and permits useful incremental coverage.
  It does not eliminate source-identity or statement-adequacy obligations.

Costs remain: repeated proof checking, maintenance of proof automation, and
potential elaboration bottlenecks. Full-P4 scalability is unestablished.
Reusable metatheorems or verified passes remain compatible with this choice.
The README states the flexibility and shared checking-cost rationale briefly;
these qualifications and the precise correctness contract stay in longer docs.

## Closest prior art: different answers for different questions

### Cogent: closest specific proof architecture

The paper's section 4.6 generates Isabelle/HOL types and functions from a
deep Cogent embedding, together with a program-specific correspondence
theorem. Its `scorres` predicate states that evaluation of the deep term
produces a value related to the shallow term. Syntax-directed rules automate
the proof. Section 4.7 then connects that shallow model to a more readable
one by equality. Section 4.3 explains composing callee correspondence results
along the call graph.

This is particularly close to our AL-interpreter-to-Lean translation,
representation relations and per-definition certificates. Cogent's complete
pipeline additionally connects the models to generated C, combining general
metatheorems with per-program proofs. We share a proof architecture, not its
entire end-to-end guarantee. Its section 4.6 implication must not be silently
read as two-way equivalence.
[Cogent: Certified Compilation for a Functional Systems Language, §4.3–4.7][cogent]

### AutoCorres: closest proof-friendly model-generation pattern

AutoCorres starts from a detailed logical representation of C and produces
a more convenient model with refinement proofs. Its first phase moves from
deeply embedded statements to a shallow monadic representation. Further
phases abstract details such as machine words and heaps. The parser supplying
its initial representation is a separate trust boundary.

The important lesson is that a usable model need not resemble the reference
closely if their relationship is proved. Its abstraction theorems can depend
on guards and nonfailure assumptions; this is not unconditional equivalence.
Our aim to preserve AL behavior, including failure distinctions, must retain
its own explicit contract rather than copy those assumptions.
[Greenaway et al., Don't Sweat the Small Stuff, PLDI 2014, §2–3][autocorres]

AutoCorres is not just historical: the separate AutoCorres2 AFP entry was
published in 2024 and records a 2025 extension. This establishes continuing
development, not that every original limitation remains or has disappeared.
[AutoCorres2 entry and change history][autocorres2]

### CakeML: close certificate construction, opposite translation direction

Myreen and Owens translate HOL functions into ML syntax and generate a
theorem connecting each translation to ML operational semantics. Section 4
develops value invariants, syntax-directed proof rules and declaration
environment assumptions. The state-and-exception extension is in section 5.
These mechanisms are directly relevant to our representations, environments
and composition of certificates.

Its translator goes from shallow logical functions to deeply embedded ML;
we go from deep AL syntax to shallow Lean definitions. Its guarantees for
supported HOL functions include termination, which cannot simply be assumed
for arbitrary AL. This proof-producing translator is distinct from CakeML's
verified machine-code compiler backend.
[Myreen and Owens, JFP 2014, §4–5][cakeml-paper],
[CakeML's architecture][cakeml]

### Wasm SpecTec: closest project purpose

SpecTec generates language artifacts from a common specification. Its
PLDI 2024 paper described prover backends as work in progress. The official
March 2025 announcement reports generated Coq/Rocq definitions supporting
ported soundness proofs for the Wasm 1.0 subset. Do not use the older paper
alone to describe the backend's current existence.

The distinction is between proving a property of the generated language
model and proving that the model corresponds to its source specification.
The cited sources report the former, not our proposed per-definition
translation certificates against a separate AL interpreter. That is a
comparison of reported guarantees, not proof that no other backend work exists.
[SpecTec, PLDI 2024, §6][spectec-paper], [official 2025 update][spectec-update]

### CompCert and the wider landscape

CompCert supplies the central ambition: semantic preservation should justify
carrying program-verification results across compilation. Its compiler-level
proof structure differs from our per-artifact approach. Its correctness
contract accounts for allowed source behaviors and undefined behavior; it
is not an unconditional identity of all source and target executions.
[CompCert manual, §1.2][compcert]

Translation validation is also an active practical approach. Alive2 checks
LLVM transformations with explicitly bounded guarantees. A September 17,
2026 preprint, Trivet, combines deterministic scaffolds and automated proof
completion to produce Lean-checked refinement or non-refinement proofs for
LLVM transformations. Its loop support is restricted. This is evidence of
ongoing work, not a claim that the preprint supersedes mature tools or
establishes our project's scalability.
[Alive2, PLDI 2021][alive2], [Trivet, §3][trivet]

Additional comparisons inspected: Skel's certified abstract machines prove
soundness of interpretations of a semantics DSL through generic metatheory,
rather than our per-definition translation proofs. K's CAV 2021 proof
generation work certifies semantic tool tasks, but explicitly retains trust
in K-to-Kore compilation. Neither should be described as the same delivered
guarantee as our goal.
[Skel, CPP 2022][skel], [K proof generation, CAV 2021, §7.2][k]

## Consequences, not a new roadmap

- Keep the certifying approach. The literature does not require a universal
  generator proof as the next step.
- Judge success by a composed theorem for a useful supported entry point,
  not merely a count of generated declarations or local certificates.
- Keep source identity, representation coverage, environments and proof
  direction explicit. Kernel acceptance alone does not choose the claim.
- Use downstream examples to evaluate usability while keeping their code
  separate from provided libraries. The field-update case lives in
  `ExampleProofs/NanoP4FieldUpdate/`; reusable proof support remains in
  `P4SpecTec.Refine`.
- The closest-approach assessment is a synthesis of the cited work, not a
  first-of-its-kind claim or an exhaustive ranking of compiler research.

[leroy]: https://xavierleroy.org/publi/compiler-certif.pdf
[cogent]: https://arxiv.org/pdf/1601.05520
[autocorres]: https://trustworthy.systems/publications/nicta_full_text/7629.pdf
[autocorres2]: https://isa-afp.org/entries/AutoCorres2.html
[cakeml-paper]: https://www.cl.cam.ac.uk/~mom22/jfp14.pdf
[cakeml]: https://cakeml.org/
[spectec-paper]: https://homepages.inf.ed.ac.uk/slindley/papers/spectec.pdf
[spectec-update]: https://webassembly.org/news/2025-03-27-spectec/
[compcert]: https://compcert.org/man/manual001.html
[alive2]: https://web.ist.utl.pt/nuno.lopes/pubs.php?id=alive2-pldi21
[trivet]: https://arxiv.org/html/2609.19583v1
[skel]: https://guillaume.ambal.fr/doc/CPP12022/cpp.pdf
[k]: https://trinhmt.github.io/home/Proof/CAV21.pdf
