# Design review: recommendations and open judgments

Date: 2026-09-25. Reviewed baseline:
`c215d102758c00b829a50085e1e271185a176613`.

Requested companion to [the prior-art comparison](../../docs/prior-arts-comparison.md).
This note records critique, suggested priorities, and questions from the review.
The user subsequently adopted the bounded direction below, now incorporated
in the design and decision register. Other recommendations remain advisory.

Completion update, 2026-09-26: PR #27 delivered the bounded field-update
consumer, including source representation and initialization, finite reference
realization, and distinct-name commutation transferred to the reference.
The baseline critique and suggested sequence below remain historical, not
authorization to resume M3 or evidence that those later suggestions were done.

## Agreed follow-up direction

Keep AL as compiler input and the handwritten Lean AL interpreter as reference.
Retain the generated P4-specific model, but establish one complete, useful
example before broader expansion. Its executable model and reference must have
the same terminating observable behavior in both directions on a declared
domain, including relevant failures and state changes. A consumer theorem must
transfer through that complete connection. Reference fidelity to upstream P4
remains a separate trust boundary.

The final proof interface is open. Use this example to identify needed
abstraction lemmas; do not build an IL backend or redesign the architecture
now. The earlier three-case AL/IL comparison and interpreter-only alternative
are possible later investigations if the example exposes a concrete problem,
not competing immediate tasks. The field-update example is now complete;
broader expansion remains paused.
Existing M3 work and gates are preserved; the first consumer proof is brought
forward from M4. See [design section 1.1](../../docs/design.md#11-agreed-direction-and-first-consumer-checkpoint).

## 1. What the project is for

The useful product is a dependable connection between a maintained P4 reference
and Lean proofs. It has two clients: people reasoning about the language itself
and people relating another model or implementation to it.

Generation reduces duplication. Certificates reduce dependence on the code
generator. A usable interface reduces the cost of downstream verification.
The project succeeds when these three benefits hold together.

A generated model that no one can reason about is incomplete as a product. A
pleasant model without a clear source connection recreates the synchronization
problem. A collection of strong local proofs without a certified entry point
does not yet provide the guarantee most clients need.

This is useful infrastructure even if the certification technique is assembled
from established methods. A research contribution needs stronger evidence:
scale, automation, semantic fidelity, consumer proofs, and maintenance under
real upstream changes. Avoid claiming novelty solely from the use of Lean or
the combination of generation and proofs.

## 2. What I would keep

- AL as the present translation boundary, with its upstream stages disclosed.
- The separate Lean reference interpreter and per-artifact certificates.
- Explicit mismatch, hard error, and partiality.
- Preservation of allocator state through failed attempts and negation.
- Independent upstream observations and quotation comparisons.
- Reproducible generation, pinned inputs, and exact axiom audits.
- Unsupported constructs rejected explicitly instead of assigned convenient
  default meanings.
- A generic core that is not tied to p4blo's particular IR or architecture.

The current stateful fixtures address real semantic hazards. This review is
not a reason to discard that work or replace it with a success-only theorem.

## 3. The largest risks

### True theorem, inadequate statement

Kernel checking establishes a proposition, not that the proposition captures
the user's intended claim. Generated types, value relations, source quotations,
and environment assumptions help determine that proposition.

Examples of gaps worth testing explicitly:

- Omit a constructor and certify all remaining generated inputs.
- Change both the generated function and its generated relation consistently.
- Quote the wrong source definition and certify a translation of that quote.
- Erase information observed by printing while proving equality under a weaker
  canonicalization relation.
- Require an environmental assumption without delivering an initialization
  theorem that satisfies it.

The repository already has a `HoldsSpec` initialization witness and independent
quotation checks. Preserve these strengths, and extend the same discipline to
representation coverage and extern implementations.

### Broad coverage without a complete consumer path

The recorded 18 refinement theorems cover functions only. This matters more
than the fraction alone: an important relation entry point may still lack its
source connection even when many helpers are certified.

Track two dimensions independently: construct coverage and certified entry
points. A small complete slice can establish more practical value than a large
set of disconnected certificates. Conversely, one carefully selected example
does not establish general full-P4 coverage.

### Proof costs growing with concrete source size

Lockstep symbolic execution is understandable and initially economical. Large
concrete definitions, case splits, and recursive groups may make it expensive.
Historical Nano refinement timings of 19–89 seconds per group are a reason to
measure, not a fresh performance result or evidence of failure.

Use generic semantic lemmas where profiling identifies repeated work. Report
generation time, elaboration time, proof-checking time, peak memory, and
incremental rebuild costs separately. Avoid optimizing the source representation
before knowing which stage dominates.

### Upstream coupling without downstream stability

Mirrored names and files help maintainers. They are not necessarily a stable
consumer API. A source refactoring can preserve semantics while disrupting many
imports and theorem statements.

Expose a small public layer once a consumer establishes what it needs. Prove
its connection to the generated layer. Keep generated provenance accessible,
but reconsider freezing every generated name as a permanent public promise.

## 4. Clarify the semantic product before expanding its claims

For each interface, state whether it describes:

1. Ordered AL execution under a specific configuration.
2. An exact relational account of that execution.
3. A sound overapproximation of successful execution.
4. Upstream declarative rules before algorithmization.
5. A P4 architecture or physical target.

These are different contracts. The present pure relation's omitted `else`
rejection premises mean that generic completeness and determinism cannot simply
be assumed. A relation can be useful without being exact, but consumers must
know which implication they can use.

The supported execution profile should also identify guards, determinism
instrumentation, caching, callbacks, externs, and observable outputs. In the
stateful setting, an instrumentation mode can consume fresh identifiers and
therefore affect comparison. Configuration is part of the semantic boundary.

Do not silently extend a result-only theorem to effects. Do not call a
finite-fuel `none` semantic divergence. Do not treat failure classification as
incidental when retry depends on it.

## 5. Suggested next steps

This was the suggested sequence at the review baseline. The first consumer
checkpoint is now complete; remaining items are advisory and require new scope.

### First: make one complete guarantee concrete

Choose a small consumer theorem and list its exact dependencies. It should
exercise a real semantic issue, such as stateful failure, a nontrivial typing
rule, or a small semantics-preserving transformation. The agreed target
requires both forward correspondence and reverse realization for its domain.

Its deliverable should package:

- A pinned source artifact and checked quotation identity.
- Input representability and output observations.
- An initialized semantic environment.
- Certificates for every reachable dependency within the stated domain.
- Extern contracts or explicit assumptions.
- The user-facing conclusion, including termination qualifications.

A forward-only certificate can transfer a property of every covered terminating
source execution, but does not complete the agreed example. Reverse realization
also permits a generated run to witness a source run. Proving both directions
does not require proving global termination for every input.

### Second: make certification coverage machine-readable

Propose a manifest containing source/export identifiers, definitions,
dependencies, supported constructs, theorem names, representation obligations,
environment assumptions, and unsupported reasons.

Separate generation success from certification success. A strict certification
mode should fail when the requested entry point lacks any required dependency
or contract. An exploratory generation mode can remain useful without being
marketed as a certificate.

### Third: establish representation adequacy

Start with one family used by the consumer proof. Specify a source validity
predicate and prove encoding validity, representability, and decoder round trips
with enough fuel. State exactly which observations respect the relation.

This is preferable to merely adding more equalities about `canon`. Equality
compatibility does not cover hinted printing, callbacks, or arbitrary metadata.

### Fourth: challenge the boundaries with mutations

Use mutations that correspond to plausible defects:

| Mutation | Evidence expected to detect it |
|---|---|
| Reorder alternatives or retry a hard error | Source correspondence proof or distinguishing upstream test |
| Reset state after mismatch | All-outcome state correspondence and state oracle |
| Drop a constructor or swap a field | Representation obligations and decoding/oracle tests |
| Change the source quotation | Independent quotation identity check |
| Change executable and relation together | Reference correspondence, not run-soundness alone |
| Collapse print provenance | Observation-specific relation and printer tests |

A mutation caught by one layer does not prove another layer is effective. Record
which boundary rejects each mutation. Existing targeted negation and oracle
sensitivity checks are useful but do not replace general generator mutations.

### Fifth: run a maintenance experiment

Upgrade across several real upstream changes and measure what requires manual
repair: the interpreter port, generator, certificates, public lemmas, and a
consumer proof. Record elapsed effort and reasons for changes, not only counts.

This is the strongest way to test whether source mirroring and generation
actually reduce the cost of keeping a mechanization current.

## 6. Statements in the current design worth revisiting

These describe positions at the reviewed baseline and the suggested changes.
The subsequent design update adopts the correctness target and bounded example
and corrects directly conflicting descriptions. Other proposals remain advisory.

| Existing position | Suggested revision |
|---|---|
| Prior prover backends are unverified pretty-printers with only partly usable output | Acknowledge substantial generated-model proofs; distinguish translation certification from model metatheory |
| A fixed count of axioms or opaque declarations characterizes another backend | Pin, reproduce, and classify counts, or omit them |
| Inspection establishes correctness and needs no proof | Mirroring supports audit; it does not mechanically establish cross-language fidelity |
| No rewriting passes | Prefer source structure, but permit justified transformations with explicit contracts |
| Every relation should get determinism | First define whether the relation is exact or overapproximating; prove determinism where it is true and useful |
| Any handwritten downstream adapter indicates failure | Measure adapter scope and maintenance; proved abstraction layers can improve usability |
| The shallow definition is total | Distinguish a Lean definition's logical status from termination of its modeled computation |
| IL/AL is first-order | Restrict this description to the certified fragment; full AL has higher-order features |
| Completeness follows once determinism is available | Reverse realization still needs an existence/termination argument |
| A universally verified translator is impractical because the elaborator is unverified | Explain the chosen cost tradeoff; formal target ASTs and validated text bridges remain possible |
| An OCaml generator could never be verified | Implementation language affects cost and tooling, not principled possibility |
| Downstream users do not shape the project | Keep semantic scope independent while using consumer proofs to validate the API |

Several passages already state the limitations accurately. The main need is to
make the opening thesis, success criteria, and later qualifications consistent.
The detailed comparison supplies the primary sources for these judgments.

## 7. Claims at the review baseline and later targets

Now: generated Nano semantics with checked internal run-soundness, finite
upstream agreement, and AL correspondence for a documented fragment. State
foundations and fixtures establish reusable boundaries; they are not generated
full-P4 certification. No claim of verified P4-to-hardware compilation follows.

Next: a consumer theorem over a complete certified slice, with representation,
configuration, and extern assumptions visible.

Eventually, if supported by evidence: an automatically regenerated Lean model
with source correspondence for a substantial P4 semantic profile and affordable
proof maintenance across upstream evolution.

P4-SpecTec remains a reasonable upstream for this goal. Its limitations should
define the supported profile rather than disappear behind the word "P4".
Independent P4 formalizations are valuable cross-checks, especially for areas
outside that profile. A disagreement is a finding to investigate, not a vote
that the majority implementation wins.

## 8. Review scope

The review and its follow-up updates are documentation-only work. The user
approved the direction recorded above; no generator, proof implementation, or
pin changed. No fresh Lean build or benchmark result is implied. The example's
later completion belongs to PR #27, not to this documentation review.
