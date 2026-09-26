# Related Work

This document places p4-spectec-lean in the literature on generated semantics,
certifying compilation and P4 verification. It explains which techniques inform
the implementation and which guarantees downstream users can expect. Sources
and implementation claims were checked on 2026-09-26; the repository baseline
is `395022a`. This is a focused comparison, not an exhaustive survey or a
claim that the project introduces a new certification methodology.

p4-spectec-lean translates a **language specification**, not individual P4
programs into switch code. Its input is P4-SpecTec's algorithmic language (AL).
Its outputs are executable Lean definitions, inductive relations and, for a
supported fragment, correspondence proofs against a Lean AL interpreter.
The intended contribution is a maintained, checked connection from an evolving
P4 specification to verification in Lean. The [design](design.md) specifies
the correctness contract and current limitations.

No single predecessor is closest in every respect:

| Work | Closest connection | Important distinction |
|---|---|---|
| Wasm SpecTec | Deriving mechanized semantics from a specification | Proofs about a generated model and proofs of its translation are separate obligations |
| Sail's Lean backend | Engineering executable semantics in Lean | Generated representation and effect choices do not themselves establish translation correctness |
| Cogent's model generation and AutoCorres | Constructing convenient models with correspondence proofs | Each phase has a specific direction, domain and assumptions |
| CakeML's proof-producing translator | Per-definition certificates and semantic value relations | Its translation goes from logical functions to ML syntax, unlike our AL-to-Lean direction |
| Petr4, P4Cub and HOL4P4 | P4 semantics, proof-oriented abstractions and architecture modeling | Their semantic boundaries and purposes differ from tracking the specification authoring toolchain |

## 1. Generating semantics from a shared specification

### SpecTec and specification alignment

Youn et al.'s *Bringing the WebAssembly Standard up to Speed with SpecTec*
describes generating documents and an interpreter from a common language
description. Its 2024 account treats theorem-prover backends as future work.
The official March 2025 update subsequently reports a Coq/Rocq backend and
ported type-soundness proofs for the Wasm 1.0 subset. The older paper alone
therefore understates the later mechanization. [SpecTec, §2–3 and §6][spectec];
[official update][spectec-update]

This makes Wasm SpecTec the closest comparator in purpose. Both projects seek
to reduce divergence between a language specification and its mechanization.
There is nevertheless an important distinction between proving type soundness
*of a generated language model* and proving that generation preserves a
*source specification's semantics*. The cited Wasm results establish the former;
our correspondence certificates target the latter at the AL boundary. These
claims are complementary. Substantial consumer proofs are evidence of model
usability, while translation proofs justify the connection to the reference.
This distinction is not a claim that every other SpecTec backend lacks
translation-correctness work.

P4-SpecTec adapts specification mechanization to executable P4 typing,
instantiation and evaluation. Its paper describes algorithmic inference rules
and the integration of mechanization into the language's governance. The
official working specification records **conditional adoption** as the P4
specification authoring toolchain. This prospective connection to specification
maintenance is the principal reason for deriving our reference from
P4-SpecTec, rather than maintaining an independent Lean definition of P4.
[P4-SpecTec, §3–4 and §7][p4spectec]; [working specification][p4-working]

The upstream connection does not remove semantic scope limits. The paper
explicitly excludes concurrency, undefined values, implementation-specific
behavior and unresolved semantics. Nor does adopting AL as input prove the
upstream parser, elaborator or algorithmization correct. For our users,
alignment means a reproducible connection to a pinned, documented reference,
not automatic coverage of every P4 behavior or unconditional authority for
every upstream implementation choice. [P4-SpecTec, §8.6][p4spectec]

### Sail and the engineering of Lean models

Sail's Lean backend is a close engineering precedent for translating large
executable semantics into Lean. The implementers' RISC-V experience report
discusses generated types, effects and recursion. The pinned backend has an
explicit rewriting pipeline; its printer supports partial and noncomputable
definitions as well as termination measures. These are backend capabilities,
not evidence that every emitted model uses those options. [Sail experience
report][sail-lean]; [pipeline][sail-pipeline]; [printer][sail-printer]

Sail demonstrates why representation choices are part of model engineering,
not incidental pretty-printing. Our preference for preserving AL structure
supports source audit, but does not establish that the resulting interface is
the easiest one for downstream proofs. A separate, proved abstraction can
serve that purpose. Similarly, Sail's effect interfaces offer a useful design
comparison without implying that P4 architecture state and AL's internal fresh
identifier counter should be modeled as the same effect.

## 2. Proof-producing translation and compiler verification

### Terminology and the role of CompCert

Leroy distinguishes proving a compiler-level correctness theorem from
producing independently checkable evidence for each translation. A certifying
compiler may emit proof terms or annotations from which a checker reconstructs
the proof. Translation validation checks individual source/target pairs; its
guarantees depend on the validator. These categories overlap: an untrusted
generator combined with a sound validator can form a certified compiler.
“Certifying” and “certified” are therefore not opposing quality levels.
[Leroy, §2][leroy]

We use **certifying compiler** for the project goal and **proof-producing
semantics translation** for its mechanism. The emphasis is on per-definition
correspondence evidence, not a universal theorem about the generator's
implementation. This choice lets the generator evolve while Lean checks its
outputs. Since the output is a reusable language model, certification costs
are incurred when building that model rather than for each downstream P4
program. The tradeoff is repeated proof checking and maintenance of proof
automation; scalability to full P4 remains to be demonstrated.

CompCert supplies the broader motivation: semantic preservation allows
properties established at one level to carry across compilation. Its verified
compilation chain connects CompCert C abstract syntax to assembly abstract
syntax. Its observable-behavior contract accounts for undefined behavior and
permitted refinements, rather than asserting unconditional equality of all
executions. This is a useful standard of explicitness, not the same artifact
or current guarantee as ours. [CompCert manual, §1.2–1.3][compcert]

### Cogent: generating a model and a compositional certificate

Cogent combines general semantic metatheorems with per-program proofs linking
C code, deep semantic representations and a convenient Isabelle/HOL model.
Its model-generation phase is particularly close to our construction. A
*deep embedding* represents syntax as data evaluated by a semantics; a
*shallow embedding* uses the host logic's functions and types directly.
Cogent generates shallow HOL definitions and a correspondence theorem for the
deep representation. In the 2016 paper's §4.6, the key implication is that
evaluation of the deep term yields a value related to the shallow result.
The construction direction should not be confused with the direction of a
refinement relation. [O'Connor et al., §2 and §4.6][cogent]

The following phase connects the generated shallow model to a more readable
one by equality. Together with the preceding phases, these proofs form an
application-level certificate rather than a collection of disconnected local
facts. This motivates two aspects of our design: composing certificates over
dependencies, and allowing a proof-friendly interface above the generated
reference. Cogent's particular restrictions and termination arguments do not
establish termination or two-way correspondence for arbitrary AL.
[O'Connor et al., §4.1–4.7][cogent] The expanded journal treatment gives the
correspondence predicate and generated theorem in §5.3.4 and discusses the
subsequent shallow-model transformations and composed certificate in
§5.3.5–5.3.6. [O'Connor et al., 2021][cogent-jfp]

### AutoCorres: abstraction with a checked connection

AutoCorres transforms detailed C semantics into a more convenient monadic
representation in Isabelle/HOL and proves correspondence. Its initial phase
translates deeply embedded statements into shallow definitions; later phases
abstract such details as heaps and machine words. This makes it another close
precedent for generating proof-oriented models with checked semantic links.
Its theorems have specific guards and nonfailure conditions, and its initial
C parser is a separate trust boundary. They should not be summarized as
unconditional equivalence. [Greenaway et al., §2–3][autocorres]

The lesson for our project is not that a reference model must always mirror
its source. Rather, a useful abstraction can differ substantially if its
relationship to the reference is proved. Our current AL-preserving interface
and a future user-oriented P4 library can therefore coexist. The separate
AutoCorres2 development, documented in the Archive of Formal Proofs, is also
a relevant implementation reference; its existence should not be taken to
mean that every limitation of the original paper remains or has disappeared.
[AutoCorres2][autocorres2]

### CakeML: certificate construction in the opposite direction

Myreen and Owens' proof-producing translator takes HOL functions to ML syntax
and proves the connection to ML operational semantics. Semantic value
invariants and declaration-environment assumptions support compositional
certificates, including state-and-exception translation. This translator is
distinct from CakeML's verified machine-code compiler backend.
[Myreen and Owens, §4–5][cakeml-paper]; [CakeML architecture][cakeml]

The direction differs from ours: HOL functions become deeply embedded ML,
whereas we turn deep AL syntax into Lean definitions. The reusable lesson is
the explicit treatment of representations, environments and callees. A
certificate should identify what makes source and target values correspond
and which declarations its proof requires. Termination conclusions remain
subject to the translator's certificate assumptions, not transferable to AL
merely because both projects generate proofs.

### Translation validation beyond generated language models

Alive2 checks LLVM transformations using SMT-based bounded translation
validation. Its loop-unrolling bounds limit the behaviors examined; successful
bounded validation is not an unrestricted equivalence theorem. It illustrates
the practical value of checking translations independently of a changing
compiler, while differing from our Lean-kernel proof boundary.
[Lopes et al., §1 and §7–8][alive2]

The September 2026 Trivet preprint uses generated proof scaffolds and automated
proof completion to obtain Lean-checked refinement or non-refinement results
for LLVM transformations, including a restricted class of loop transformations.
It is a recent example of separating proof search from proof checking, not
evidence that arbitrary transformations or our full-P4 workload are tractable.
Its preprint status and restricted evaluation matter when comparing it with
established systems. [Liao et al., §3–4][trivet]

## 3. P4 semantics and downstream verification

The choice of P4-SpecTec is a choice of reference provenance, not a claim that
other P4 models are inferior. A semantics designed for interpreter execution,
a small verification IR and an architecture-aware operational model address
different needs. Prior P4 work helps identify the abstractions users may want
above our generated reference.

Petr4 combines an architecture-parameterized P4 interpreter with a formal
Core P4 calculus whose metatheory establishes type-preserving termination.
The paper explicitly distinguishes these artifacts and does not formally relate the
interpreter to the core calculus. Core P4's metatheory therefore cannot be
read as a correctness theorem for the entire interpreter. For this project,
Petr4 is valuable both as a semantic comparison and as an example of why a
useful core calculus does not by itself settle its connection to a broader
language implementation. [Petr4, §1 and §3][petr4]

P4Cub deliberately reduces P4 to a small verification-oriented intermediate
language in Coq, retaining P4-specific constructs such as headers, parsers and
tables. Its separation of expressions from effectful statements and its
mechanized expression-level results are relevant to proof-friendly downstream
models. The paper's body distinguishes completed expression and l-expression
metatheory from unfinished statement-level soundness and transformation
preservation. It is not evidence of a fully verified surface-P4 compiler.
[P4Cub, §6.1–6.2][p4cub]

HOL4P4 provides heapless small-step semantics with externs, concurrency and
architectural composition in HOL4, together with progress, preservation and
type-soundness results and a derived executable semantics.
[Alshnakat et al.][hol4p4-paper] It is particularly relevant where verification must
include the execution environment rather than a language helper in isolation.
Its prover, semantic organization and supported architecture interfaces differ
from ours; using its results with our Lean model would require an explicit
semantic bridge, not a change of file format. [HOL4P4][hol4p4]

Verifiable P4 supplies a sound Coq program logic for stateful control blocks
and connects P4 programs to functional models. Its operational semantics also
includes parsing and deparsing, but the program logic does not cover those
components. The extracted interpreter is proved sound against the operational
semantics; resolving undefined values to zero intentionally selects only some
allowed behaviors. This is a useful example of directional correspondence and
of a user-oriented proof layer above reference semantics. Its certificates
concern P4 program behavior, whereas ours concern translation of the language
model. [Wang et al., §3.3–3.4 and §7][verifiable-p4]

These approaches can complement p4-spectec-lean. A downstream project could
choose a compact P4Cub-inspired model or an architecture-oriented semantics,
then establish correspondence with the generated reference for a declared
domain. Such a connection is a potential use of this project, not a delivered
equivalence with any of these tools. Language version, extern behavior,
representation and observable state would all need to agree.

## 4. Consequences for this project and its users

The closest proof architectures are Cogent's model-generation phases and
AutoCorres; Wasm SpecTec is closest in specification-maintenance purpose.
CakeML contributes a complementary account of compositional proof production,
while Sail and the P4 mechanizations inform model engineering and usability.
This assessment is our synthesis of the sources, not a ranking of their
overall assurance or maturity.

Three obligations follow from that comparison.

**Connect the intended source to the theorem.** Kernel checking validates the
stated proposition. It does not establish that a quoted AL definition is the
intended exported definition or that generated types cover the claimed source
domain. Our independent quotation check addresses source identity through
runtime comparison; representation and initialization proofs address separate
logical obligations. Upstream frontend correctness and fidelity of the Lean
interpreter port remain outside the generated correspondence theorem.

**State the implication consumers can use.** Our current generated refinement
theorems relate every terminating reference outcome to a generated outcome,
including the modeled failure kinds. Reference fuel exhaustion is not a
termination or divergence theorem. The reverse direction requires a finite
reference execution witness; determinism alone does not provide it. Likewise,
run-soundness from executable code to a generated relation is not automatically
equivalence between that relation and the reference. Consumers should use
the proved direction, domain and environment, not infer a stronger contract
from the word “certificate”. See the [verification contract](design.md#5-verification-and-validation).

**Evaluate complete uses, not just generated coverage.** At this baseline,
[generated AL refinement](../NanoP4Spec/Refinement.lean) covers 18 of 153 Nano
definitions in one direction. The handwritten
[field-update certificate](../NanoP4Proofs/FieldUpdate/Certificate.lean)
additionally establishes representation coverage, initialization and two-way
terminating correspondence on its scalar domain. The
[example](../NanoP4Proofs/FieldUpdate/Example.lean) transfers distinct-name update
commutation to reference executions. It does not certify arbitrary P4
assignment reordering, all Nano-P4, or full P4.

For developers, useful evaluation therefore includes certified dependency
chains, downstream proof effort, checking time and memory, and repair effort
across actual upstream changes. For users, the important question is whether
the entry point and behaviors their proof needs lie inside a documented,
composed correctness argument. Neither successful generation nor finite
differential tests alone answers that question.

## References

Paper section numbers above refer to the linked versions. Project pages and
the working specification are dated observations, not immutable publications.
Backend source links are pinned. Preprints and implementation reports are
identified separately from conference and journal papers.

- Youn et al. *Bringing the WebAssembly Standard up to Speed with SpecTec*.
  PLDI, 2024. [Paper][spectec].
- Andreas Rossberg. *SpecTec has been adopted*.
  Official update, 27 March 2025. [Article][spectec-update].
- Lee et al. *P4-SpecTec: Integrating a Language Mechanization Framework into
  the Real-World P4 Specification*. arXiv:2608.00639v1, 2026.
  [Preprint][p4spectec]. P4 Language Consortium. [Working specification][p4-working].
- Sail Lean backend implementers. *Bringing RISC-V Semantics to Lean*.
  [Implementation report][sail-lean], 2 December 2025. Backend commit `42d1ec6`:
  [pipeline][sail-pipeline], [printer][sail-printer].
- Xavier Leroy. *Formal Certification of a Compiler Back-end, or:
  Programming a Compiler with a Proof Assistant*. POPL, 2006.
  [Paper][leroy]. [CompCert manual, chapter 1][compcert].
- O'Connor et al. *Cogent: Certified Compilation for a Functional Systems
  Language*. arXiv:1601.05520, 2016. [Preprint][cogent]. Expanded treatment:
  O'Connor et al. *Cogent: uniqueness types and certifying compilation*.
  Journal of Functional Programming 31, e25, 2021. [Paper][cogent-jfp].
- Greenaway et al. *Don't Sweat the Small Stuff: Formal Verification of C Code
  Without the Pain*. PLDI, 2014. [Paper][autocorres].
- *AutoCorres2*. Archive of Formal Proofs, 2024; subsequent changes recorded
  in the entry. [Artifact and history][autocorres2].
- Magnus O. Myreen and Scott Owens. *Proof-producing translation of
  higher-order logic into pure and stateful ML*. Journal of Functional
  Programming, 2014. [Paper][cakeml-paper]. [CakeML project][cakeml].
- Lopes et al. *Alive2: Bounded Translation Validation for LLVM*.
  PLDI, 2021. [Paper][alive2].
- Liao et al. *LLVM Translation Validation Automated with Large Language
  Models and Lean*. arXiv:2609.19583v1, 17 September 2026. [Preprint][trivet].
- Doenges et al. *Petr4: Formal Foundations for P4 Data Planes*.
  PACMPL 5 (POPL), Article 41, 2021. [Paper][petr4].
- Peterson et al. *P4Cub: A Little Language for Big Routers*.
  CPP, 2023. [Paper][p4cub].
- Alshnakat, Lundberg, Guanciale and Dam. *HOL4P4: Mechanized Small-Step
  Semantics for P4*. PACMPL 8 (OOPSLA1), Article 102, 2024.
  [Publication record][hol4p4-paper]; [implementation and documentation][hol4p4].
- Wang et al. *Foundational Verification of Stateful P4 Packet Processing*.
  ITP, 2023. [Paper][verifiable-p4].

[spectec]: https://homepages.inf.ed.ac.uk/slindley/papers/spectec.pdf
[spectec-update]: https://webassembly.org/news/2025-03-27-spectec/
[p4spectec]: https://arxiv.org/html/2608.00639v1
[p4-working]: https://p4lang.github.io/p4-spec/docs/P4-16-working-spec.html
[sail-lean]: https://lindylabs.net/articles/risc-v-semantics-lean
[sail-pipeline]: https://github.com/rems-project/sail/blob/42d1ec6b32dd09312d91efa6a490ed7e9193b0c7/src/sail_lean_backend/sail_plugin_lean.ml
[sail-printer]: https://github.com/rems-project/sail/blob/42d1ec6b32dd09312d91efa6a490ed7e9193b0c7/src/sail_lean_backend/pretty_print_lean.ml
[leroy]: https://xavierleroy.org/publi/compiler-certif.pdf
[compcert]: https://compcert.org/man/manual001.html
[cogent]: https://arxiv.org/pdf/1601.05520
[cogent-jfp]: https://www.pure.ed.ac.uk/ws/portalfiles/portal/237868824/Cogent_O_CONNOR_DOA01092021_VOR_CC_BY.pdf
[autocorres]: https://trustworthy.systems/publications/nicta_full_text/7629.pdf
[autocorres2]: https://isa-afp.org/entries/AutoCorres2.html
[cakeml-paper]: https://www.cl.cam.ac.uk/~mom22/jfp14.pdf
[cakeml]: https://cakeml.org/
[alive2]: https://users.cs.utah.edu/~regehr/alive2-pldi21.pdf
[trivet]: https://arxiv.org/html/2609.19583v1
[petr4]: https://www.cs.cornell.edu/~jnfoster/papers/petr4.pdf
[p4cub]: https://www.cs.cornell.edu/~jnfoster/papers/p4cub.pdf
[hol4p4]: https://github.com/kth-step/HOL4P4
[hol4p4-paper]: https://2024.splashcon.org/details/splash-2024-oopsla/9/HOL4P4-mechanized-small-step-semantics-for-P4
[verifiable-p4]: https://www.cs.princeton.edu/~appel/papers/FoundationalVerificationP4.pdf
