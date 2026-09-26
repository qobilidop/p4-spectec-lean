# Prior-art comparison

Review date: 2026-09-25. Repository baseline:
`c215d102758c00b829a50085e1e271185a176613`.

This document compares **p4-spectec-lean**, the AL-to-Lean compiler, with
related work. It is an assessment and a set of recommendations, not a
replacement for the agreed [design](design.md). Implementation observations
refer to the baseline above; proposed guarantees are not delivered guarantees.
The review inspected code and recorded validation evidence but did not rerun
the build or benchmarks.

**Subsequent agreed direction (2026-09-25):** retain the AL backend and the
handwritten Lean reference interpreter. Before broader expansion, establish
two-way agreement on terminating observable behavior for one complete example
and transfer a useful consumer theorem through it. No IL backend or broad
redesign is scheduled. The [design checkpoint](design.md#11-agreed-direction-and-first-consumer-checkpoint)
and [correctness contract](design.md#5-verification-and-validation) govern
this direction; the remaining review recommendations below are advisory.

**Completion update (2026-09-26):** the checked
[field-update consumer](../NanoP4Proofs/FieldUpdate/Example.lean) now supplies
both directions on its scalar source domain, concrete initialization and
representation obligations, and reference-level distinct-name commutation.
This is a bounded handwritten proof, not expanded general certificate coverage.
The baseline assessments and prospective recommendations below are historical;
broader M3 remains paused.

## Assessment

The project addresses a useful problem: obtaining a usable Lean model of an
evolving P4 specification while checking that translation preserves a stated
semantics. Maintaining a separate handwritten model creates an ongoing
synchronization burden. Generation can reduce that burden; certificates can
make the semantic connection explicit.

The overall approach is promising. Keep AL as the current source boundary,
explicit partiality and failure, and per-artifact certificates. Strengthen the
representation contracts, composition of certificates, and meaning of the
relational interface. Evaluate proof usability and maintenance as seriously as
generation coverage.

There is no single prior project against which every choice should be judged:

| Comparator | Closest aspect | Principal lesson |
|---|---|---|
| Wasm SpecTec prover backends | Generating mechanized semantics from a specification language | Judge output by substantial proofs and regeneration costs |
| Sail Lean backend | Large executable semantics in Lean | Account for effects, recursion, target-specific normalization, and usability |
| Cogent | Compilation accompanied by formal models and correspondence evidence | Compose general metatheorems and per-artifact certificates across representations |
| CakeML proof-producing translator | Producing a theorem for each translated definition | Make value invariants, environments, and callee certificates explicit |
| Petr4, P4Cub, HOL4P4 | The P4 semantics and abstractions a consumer might want | Separate reference-language fidelity from proof-oriented IR and architecture modeling |

The strongest possible contribution is a practical, maintained connection from
an evolving executable specification to downstream proofs. Neither generating
Lean nor producing translation certificates is, by itself, a new methodology.

## 1. Closest direct comparator: Wasm SpecTec

Wasm SpecTec is the closest project-level comparator: a language specification
feeds generated artifacts, including prover representations. Its Rocq output
has supported WebAssembly 1.0 and 2.0 type-soundness proofs. It should therefore
not be dismissed as merely a pretty-printer producing unusable output.
[WebAssembly mechanization project][wasm-proofs]

The inspected Rocq branch uses a substantial normalization pipeline, including
type-family removal, totalization, treatment of `else`, pattern simplification,
and conversion of definitions to relations. The pipeline reflects the mismatch
between the source specification and the target logic.
[Pinned backend pipeline][wasm-pipeline]

p4-spectec-lean starts after upstream algorithmization. It inherits executable
dataflow and generates both computations and relations, with a separate AL
interpreter serving as the certificate reference. This is a useful difference,
but some normalization work has moved upstream rather than disappeared.

The comparison should distinguish two kinds of theorem:

- A theorem *about the generated language model*, such as type soundness.
- A theorem *connecting the generated model to its source representation*.

Neither substitutes for the other. p4-spectec-lean emphasizes the second;
Wasm's substantial consumer proofs are an important benchmark for the first.

**Recommendation:** demonstrate both a complete translation certificate for a
useful slice and a nontrivial proof using that slice. Do not use raw counts of
axioms or opaque declarations from changing branches as a quality ranking.
Such counts need a pinned artifact and a classification of what each
declaration assumes, including deliberately abstract source operations.

## 2. Closest Lean engineering comparator: Sail

Sail's Lean exporter faces similar issues with generated types, effects,
recursion, and large models. Its implementation has an explicit rewriting
pipeline, including mapping realization, pattern transformations, and effect
handling. The experience report identifies practical costs in translating
representations and supporting generated definitions.
[Sail pipeline][sail-pipeline], [Lean exporter experience][sail-lean]

The inspected printer supports configurable partial and noncomputable
definitions as well as emitted termination measures. Those options do not
establish that a particular ISA model uses them. Its effect library separates
effect descriptions from interpretations, offering a useful reference for
modular semantic interfaces.
[Sail printer][sail-printer], [effect library][sail-effects]

p4-spectec-lean deliberately uses a smaller explicit result model:
`Option (Except Fail α)` in the pure case, with state in the stateful case.
This distinguishes retryable mismatch, hard error, and partial computation with
no result.
That simplicity is valuable when it matches AL.

The effects are not identical in purpose. AL's fresh counter is a metalanguage
execution effect. P4 architecture state belongs to the modeled language and
its target. Sail's architectural effects should inform modularity without
encouraging these layers to be conflated.

**Recommendation:** borrow Sail's willingness to adapt representations to the
prover and to separate effect interfaces from handlers. Preserve explicit
contracts for each adaptation. Avoid adopting a larger effect framework until
an actual consumer needs it.

## 3. Closest certification precedents: Cogent and CakeML

Cogent produces executable C, a convenient logical model, and correspondence
evidence. Its proof architecture combines general language-level results with
per-program validation through intermediate representations. Its foreign
function work makes the obligations of external implementations explicit and
composes their proofs with generated certificates.
[Cogent][cogent], [foreign-function verification][cogent-ffi]

The relevant lesson is that certificates should compose into an application
theorem. A collection of locally proved definitions is useful infrastructure,
but clients need a theorem over their entry point and its dependencies.
Cogent also demonstrates that a convenient model may legitimately differ from
an implementation when their relationship is proved.

CakeML's proof-producing translator connects HOL functions to a deep ML
semantics through per-function certificates. Its value invariants relate
logical values to semantic values, including functions; environment assumptions
identify the declarations on which a certificate depends. The work includes
state-and-exception translation. This translator must be distinguished from
CakeML's separately verified compiler to machine code.
[CakeML translator][cakeml]

p4-spectec-lean translates in a different direction: from a deep AL description
to shallow Lean definitions. Nevertheless, reusable semantic rules,
representation invariants, and composition through callee certificates apply
directly. CakeML's termination guarantees for supported HOL functions should
not be imported unchanged into a setting with potentially diverging AL.

**Recommendation:** keep per-artifact certification. Introduce general lemmas
where repeated unfolding becomes expensive or fragile, and compose them with
concrete certificates. Do not require either a universal compiler proof or
fully concrete symbolic execution as an exclusive strategy.

## 4. Critical technical choices

### 4.1 Source boundary: AL rather than IL or SL

The current pipeline is:

```text
P4-SpecTec source → parsing/elaboration → IL → algorithmization → AL
                                                               │
                                                        export/decoding
                                                               │
                                                  generated Lean + proofs
```

AL retains rule structure while exposing execution structure. It is also the
input to the upstream interpreter being mirrored. These properties make it a
reasonable boundary for the current project.

Consuming IL would require another account of algorithmization. Consuming SL
would include more upstream structuring and control-flow transformation in the
input's provenance and make individual rule correspondence less direct. Neither
alternative is inherently wrong, but neither currently offers a demonstrated
benefit sufficient to justify changing direction.

The certificate begins at AL. It does not prove that parsing, elaboration, or
algorithmization preserves the original specification's meaning. This boundary
must remain visible even if P4-SpecTec becomes an authoritative upstream.

### 4.2 Mirroring versus normalization

Mirroring names, constructor order, and file layout supports audit and upstream
maintenance. It is not a proof of semantic preservation. Byte strings, machine
integer wrap, evaluation order, and exception handling can differ even between
similar-looking programs.

The better policy is: preserve source structure by default, and permit a
transformation when its benefit and semantic obligation are explicit. Maintain
provenance through it. A small checked transformation can be easier to trust
than extensive target-specific behavior hidden in an emitter.

Avoid treating "no passes" as an independent correctness claim. Likewise, a
handwritten adapter with a proved contract is not automatically a failure of
the project. Its size, maintenance burden, and role matter.

### 4.3 What the current refinement establishes

The definition in [the refinement calculus](../P4SpecTec/Refine/Calc.lean) is:

```lean
Refines P m n :=
  ∀ r, m.run = some r →
    ∃ r', n.run = some r' ∧ ResRel P r r'
```

Here `m` is the reference interpreter and `n` the generated computation.
`ResRel` requires equal failure kinds or related success values. Generated
theorems quantify over interpreter fuel; exhaustion supplies no premise.

Thus the direction is:

```text
reference produces a terminating outcome
    → generated code produces a corresponding outcome
```

This direction is useful. Given adequate input representations, a covered
entry point and dependencies, and a property true of all relevant generated
outcomes, it transfers that property to terminating reference executions.
Combining it with run-soundness can similarly transfer a universal property
proved over the generated relation. Such a composition is a proposed consumer
theorem; relation refinement is not part of the recorded Nano coverage.

The converse has a different use:

```text
generated code produces an outcome
    → some reference fuel produces a corresponding outcome
```

It permits generated runs to serve as witnesses of reference behavior. The
current direction alone does not exclude generated termination when the
reference never terminates. Determinism does not establish the missing
termination or converse.

**Recommendation, now adopted for the first complete example:** name and
document both capabilities and establish both directions for its supported
domain. The existing one-way theorem remains useful and is not discarded;
the stronger target was not delivered at this review's baseline. The bounded
field-update completion recorded above does not establish it for other inputs.

### 4.4 Executable semantics and inductive relations

The dual interface is valuable: execution supports experiments, while inductive
relations support inversion and rule-based reasoning. But shared generation
does not imply semantic equivalence.

The current pure [Prop generator](../P4SpecTec/Codegen/Props.lean) omits prior
groups' rejection conditions from an `else` constructor. The resulting relation
can therefore overapproximate ordered execution. Conceptually, an ordinary
rule returning `0` and an unrestricted fallback returning `1` could yield both
relational results while execution selects only `0`. This is an illustrative
encoding example, not a claim that a particular pinned P4 rule has that form.

Run-soundness can still hold. Completeness or relational determinism may fail.
Choose an explicit contract:

| Interface | Intended meaning | Useful guarantee |
|---|---|---|
| Exact execution judgment | Includes priority, failures, and relevant state | Correspondence with the executable result |
| Overapproximating rule relation | Admits at least every successful execution | Universal properties imply execution properties |

An overapproximation is not automatically the upstream declarative semantics;
that requires a separate connection. Stateful rejected-prefix and iteration
fixtures address part of this problem, but do not yet establish the contract
for generated full P4.

### 4.5 Recursion, partiality, and failures

`partial_fixpoint` is an appropriate way to represent potentially diverging AL
without demanding a global termination proof. It provides logical equations
and an induction mechanism for partial correctness. Treating failure as data
keeps retries distinct from divergence.

On the reference side, `none` at one fuel is exhaustion, not proof of semantic
divergence. On the generated side it represents undefined computation in the
partial model. These should not be described interchangeably.

State belongs below failure when failed attempts consume fresh identifiers.
Correctness then concerns post-state on mismatch and hard error as well as on
success. Rollback would be a different semantics.

Keep this design. Use structural recursion where it improves reasoning, and
remove helper cutoffs that return ordinary semantic answers on exhaustion
before claiming coverage of those operations.

### 4.6 Representation adequacy

The current [value relation](../P4SpecTec/Refine/Value.lean) compares canonical
source values with canonical encodings of generated values. This is convenient
for the certified fragment, but generated types and their encodings contribute
to the theorem's statement.

A missing generated constructor can shrink the theorem's domain while leaving
its proof valid. Equality after erasing notes also does not imply agreement of
an operation that observes those notes, such as hinted printing. AL itself has
higher-order features; only the currently certified fragment is first-order.

Add obligations with explicit source typing and environmental assumptions:

1. Encoded generated values satisfy the relevant source validity predicate.
2. Every source value in the claimed domain has a related representation.
3. Encoding and decoding round-trip, with sufficient decoder fuel.
4. Permitted observations respect the representation relation.

These need not all use one universal relation. A relation suitable for equality
may require strengthening for printing or callbacks.

### 4.7 Externs and semantic environments

A typeclass supplies operation signatures; semantic laws must be supplied
separately. An extern correspondence contract should cover related inputs,
outputs, state, failures, and callbacks or events where relevant.

Likewise, a theorem conditional on a global definition table must be connected
to the actual initialized environment. The existing `HoldsSpec` initialization
witness is useful: these assumptions are not simply left without an instance.
The next step is to package source identity, environment construction, and
dependency certificates into a usable entry-point theorem.

### 4.8 Text emission and the trust boundary

Emitting committed, reproducible Lean modules supports review and incremental
builds. The kernel checks the elaborated theorem and definitions, so a bug in
proof search cannot silently prove an invalid proposition within Lean's logic.
It can still produce a valid theorem about an unintended quotation, domain,
or interface. Source identity and statement adequacy require their own checks.

The existing independent quotation comparison is useful runtime evidence. It
is not a kernel proof that the theorem's quoted input is the external input.

An unverified elaborator is not a principled impossibility result for universal
compiler verification: one could verify a translation over a formal target AST
and validate its text bridge. That would be additional work. Per-artifact
certification is a sensible choice without claiming that alternatives cannot
be verified, or that an OCaml implementation could never be verified.

## 5. Is P4-SpecTec the right P4 upstream?

The answer depends on the goal. For tracking an evolving executable language
specification, P4-SpecTec is a defensible current choice. For a deliberately
small verification IR or an architecture semantics, other projects offer
different advantages.

| Source | Relevant strengths | Qualification for this project |
|---|---|---|
| P4-SpecTec | Executable typing, instantiation, and evaluation; connection to specification authoring | AL and its toolchain become part of the reference boundary |
| Petr4 | P4 interpreter and a formal Core P4 calculus | Core metatheory does not certify the entire interpreter/frontend |
| P4Cub | Small proof-oriented P4 IR; separates expression computation from statement effects | A good abstraction design, not a drop-in equivalent of full surface P4 |
| HOL4P4 | Mechanized small-step semantics, architecture integration, executable reasoning | A different semantic organization and prover ecosystem, requiring an explicit bridge |

P4-SpecTec's paper targets P4 1.2.5 and states exclusions including concurrency,
undefined values, implementation-specific behavior, and unresolved semantics.
Its corpus comparison is evidence about tested coverage under specific versions
and exclusions, not a proof that its semantics is superior in every dimension.
[P4-SpecTec paper][p4spectec]

The official working specification records conditional adoption of P4-SpecTec
as an authoring toolchain. The conditions and transition matter; this is not
unconditional authority for every generated behavior.
[P4 working specification][p4-working]

Petr4's interpreter and Core P4 calculus are distinct artifacts. P4Cub's paper
proves selected metatheory and expression-transformation results while leaving
broader statement-level obligations for future work. Neither should be cited
as a fully verified surface-P4 compiler. HOL4P4 provides a valuable comparison
for architecture and operational modeling.
[Petr4][petr4], [P4Cub][p4cub], [HOL4P4][hol4p4]

**Recommendation:** retain P4-SpecTec provisionally, with a documented supported
semantic profile. Use the other P4 projects as independent comparisons and
sources of abstractions. A downstream project can use a P4Cub-inspired IR and
HOL4P4-inspired architecture model while relating its supported behaviors to
the generated P4-SpecTec reference. p4-spectec-lean itself need not become that
IR or architecture framework.

Revisit the upstream choice if required semantics remain unavailable, upstream
changes repeatedly defeat affordable regeneration, or an alternative offers a
demonstrably better maintained and usable reference for the intended domain.

## 6. Current evidence and appropriate claims

At the reviewed baseline, Nano generation covers 161 types, 76 functions, and
77 relations in 48 modules. Recorded evidence includes 98 run-soundness
theorems, 18 AL refinement theorems covering 18 of 153 callables, and two
determinism theorems. All 18 refinement certificates concern functions; none
concerns a relation. The 98 count includes individual and recursive-group
theorems and must not be read as 98 independently certified source callables.

The recorded differential tests agree on 78 verdicts and 48 successful output
contexts, and 342 quotations match the normalized exported source. These are
finite observations. Full-P4 export and reconnaissance exist; generated
stateful full-P4 certification does not. State calculi and bounded fixtures
should be reported separately from generated production coverage.

The intended description is:

> A certifying compiler from P4-SpecTec AL to executable and relational Lean
> semantics, supporting verification against an evolving P4 specification.

For the present implementation, qualify the certification coverage. Avoid an
unqualified claim of a verified compiler: there is no universal correctness
theorem for the whole generator, and per-output certification is incomplete.
Also distinguish this specification compiler from a compiler taking P4 programs
to switch code.

The most useful next evidence would be:

- A complete certified dependency chain for a meaningful entry point.
- A consumer theorem with explicit representations, environment, and externs.
- Mutation tests that challenge source identity and theorem domains as well as
  generated control flow.
- Clean and incremental proof-checking costs, including memory.
- Actual upstream upgrades measuring repair effort and proof stability.

These would substantiate usefulness and maintainability more directly than
generated line counts or a blanket absence of handwritten adapters.

## Sources

Technical comparisons use primary papers, project documentation, and source.
The two backend source inspections are pinned below; project pages and working
specifications are observations as of the review date. Recommendations and
judgments about p4-spectec-lean are this review's conclusions.

- [WebAssembly mechanization project][wasm-proofs].
- [Wasm SpecTec Rocq pipeline, commit `2d3d3d9`][wasm-pipeline].
- [Sail Lean pipeline, commit `42d1ec6`][sail-pipeline];
  [printer at the same commit][sail-printer].
- [Bringing RISC-V Semantics to Lean][sail-lean].
- [Lean Sail effect library, commit `c816ea7`][sail-effects].
- [Cogent: Certified Compilation for a Functional Systems Language][cogent].
- [Overcoming Restraint: Composing Verification of Foreign Functions with Cogent][cogent-ffi].
- [Proof-producing translation of higher-order logic into pure and stateful ML][cakeml].
- [P4-SpecTec paper, version 1][p4spectec]; [P4 working specification][p4-working].
- [Petr4: Formal Foundations for P4 Data Planes][petr4].
- [P4Cub: A Little Language for Big Routers][p4cub].
- [HOL4P4 implementation and documentation][hol4p4].

[wasm-proofs]: https://vtss.doc.ic.ac.uk/research/webassembly.html
[wasm-pipeline]: https://github.com/Wasm-DSL/spectec/blob/2d3d3d9c4c58abe62af134265beb0c99df5d8a18/spectec/src/exe-spectec/main.ml
[sail-pipeline]: https://github.com/rems-project/sail/blob/42d1ec6b32dd09312d91efa6a490ed7e9193b0c7/src/sail_lean_backend/sail_plugin_lean.ml
[sail-printer]: https://github.com/rems-project/sail/blob/42d1ec6b32dd09312d91efa6a490ed7e9193b0c7/src/sail_lean_backend/pretty_print_lean.ml
[sail-lean]: https://lindylabs.net/articles/risc-v-semantics-lean
[sail-effects]: https://github.com/rems-project/lean-sail/blob/c816ea7ad03cce98d51acee252540fd4215fede8/Sail/ArchSem.lean
[cogent]: https://arxiv.org/abs/1601.05520
[cogent-ffi]: https://trustworthy.systems/publications/papers/Cheung_OR_22.pdf
[cakeml]: https://cakeml.org/jfp14.pdf
[p4spectec]: https://arxiv.org/html/2608.00639v1
[p4-working]: https://p4lang.github.io/p4-spec/docs/P4-16-working-spec.html
[petr4]: https://www.cs.cornell.edu/~jnfoster/papers/petr4.pdf
[p4cub]: https://www.cs.cornell.edu/~jnfoster/papers/p4cub.pdf
[hol4p4]: https://github.com/kth-step/HOL4P4
