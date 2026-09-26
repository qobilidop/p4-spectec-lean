# Design

This document describes the intended system, not its implementation status.
[Certification](certification.md) explains what users can rely on today;
[Performance](performance.md) records measured costs;
[Related Work](related-work.md) provides research context.
Development procedures belong in [AGENTS.md](../AGENTS.md).

## 1. Purpose and scope

Generate a usable P4 semantics in Lean from P4-SpecTec, with checked proofs
connecting generated execution to an explicit Lean reference interpreter for
P4-SpecTec's algorithmic language (AL). The model should follow specification
changes and serve both program verification and equivalence proofs for other
P4 models.

The compiler translates a **language specification**, not individual P4
programs. Programs are data interpreted by the resulting model. Certification
is performed when building that model, not again for every program or packet.

Success requires four distinct kinds of evidence: coverage of the declared
specification profile, executable correspondence, alignment with upstream,
and useful downstream proofs. Generating valid Lean alone is insufficient.
Partial profiles must state their exclusions and must not be described as
complete P4 certification.

Non-goals are a P4 parser in Lean, compilation to machine code, verification
of physical devices, and a universal correctness theorem for the generator.
Upstream parsing, elaboration and algorithmization remain outside the
translation proof. Certification does not prove arbitrary P4 programs safe.

## 2. Principles

### 2.1 Correct by construction first, proofs second

Preserve upstream structure, names and provenance so differences are easy to
audit. Prefer direct, local encodings over another independently designed
semantics. Mirroring is a way to manage trust, not proof that the port is
correct; correspondence proofs and differential tests remain necessary.

### 2.2 Independently checkable claims

The generator proposes definitions, statements and proof scripts; Lean checks
the resulting proof terms. Make the statement, source domain and assumptions
inspectable. Missing contracts and failed proofs must not silently weaken a
claim or introduce defaults.

### 2.3 Preserve observations, then compose

Keep success, retryable mismatch, hard error and nontermination distinct.
Preserve relevant state even through failed attempts. Definition-level proofs
become usable guarantees only when combined with representation coverage,
dependency contracts, initialization and explicit observations.

## 3. Why AL?

The upstream specification pipeline is:

```text
.watsup → parse → EL → elaborate → IL → algorithmize → AL → structure → SL → prose
                                                      │
                                                      └→ this compiler
```

AL retains rule structure while exposing execution order. This supports both
generated logical relations and run functions, with upstream's AL interpreter
as a concrete porting reference and test oracle. Shared IL syntax modules are
needed because AL reuses those types; they do not imply a second IL backend.

An IL backend would need another account of binding and side conditions.
An SL backend would put later structuring inside the trusted source pipeline.
AL is an engineering choice, not the only viable boundary. The upstream
[`pass.ml`](../upstream/p4-spectec/p4spec/lib/pass/pass.ml) defines these stages.

## 4. Architecture

```text
                         pinned AL export
                                │
                         decoded AL syntax
                        ┌───────┴─────────┐
                        ▼                 ▼
                 Lean interpreter      generator
                        │                 ├→ typed executable model
                        │                 ├→ logical relations and quotations
                        │                 └→ correspondence proof scripts
                        └──────────┬──────────────┘
                                   ▼
                        Lean elaboration + kernel
                                   │
                          model + checked proofs
                                   ▼
                           downstream verification
```

The reference and generated paths share runtime support where appropriate.
Their agreement therefore does not independently validate that shared code
against upstream; differential testing addresses a separate boundary.

### 4.1 Generation and execution

Emit ordinary Lean source with traceable names and source-file ownership.
Place mutually recursive dependency groups together. Separate executable
modules from certificate modules so clients need not import proof automation
merely to use the model.

**Recursion strategy:** nonrecursive computations use ordinary definitions;
recursive ones use `partial_fixpoint` with monotone effects and checked
unfolding principles, not unchecked `partial`. The reference interpreter
uses fuel to support a direct recursive port and proof induction.

Choose one callable effect interface per specification from its declarations.
Pure specifications use `Eval := ExceptT Fail Option`; fresh-state
specifications thread state uniformly through calls and callbacks using
`ExceptT Fail (StateT FreshState Option)`. State below failure preserves
allocations made by rejected alternatives. Session reset is explicit.
Mixed signatures would require a sound effect analysis.

Relations expose both `R.run` and a logical `R`, connected by
`run_sound`: successful execution implies a logical derivation.
The converse and determinism are separate obligations. Extern signatures
likewise do not establish implementation correctness: certificates need
contracts for reachable externs and builtins.

### 4.2 Library boundaries

Reusable reference semantics and proof support must not depend on a generated
P4 model or consumer example. Generated models depend on that support;
consumer libraries and examples depend on the models in one direction.
Examples keep their walkthroughs and tests beside their code.

Generated identifiers preserve source provenance. Stable client wrappers may
offer better proof ergonomics, provided their connection to generated
definitions is proved. A wrapper that changes the domain or observations
needs a new semantic contract.

## 5. Verification and validation

The target is agreement of **terminating observable behavior** between the
generated executable and the Lean AL reference, on a declared source domain.
Current coverage is documented in [Certification](certification.md).

### 5.1 The refinement theorem

Fix an entry point, corresponding environments, configuration and initial
state `s`. Let `Rin(v, x)` relate reference and generated inputs.
Write `I(k, v, s)` for reference execution with fuel `k` and `G(x, s)`
for generated execution. Omit state for a pure profile.

For every admitted related input pair, require:

```text
Forward: I(k, v, s) = some r
         ⇒ ∃ q, G(x, s) = some q ∧ Rout(r, q), for every k.

Reverse: G(x, s) = some q
         ⇒ ∃ k r, I(k, v, s) = some r ∧ Rout(r, q).
```

`Rout` relates success values, preserves failure kinds, and requires exact
final fresh-state counters for the explicit-state profile. Other observations,
such as printed text or packets, require their own contracts.

Neither direction requires total termination. Reverse correspondence needs
a finite reference witness, not just determinism. Exhaustion at one fuel is
not semantic failure or evidence of divergence; reasoning across bounds must
justify stability of defined results.

**Failure vs divergence:** sequential choice retries only `Fail.unmatch`;
`Fail.err` stops it. The outer `none` means no terminating result in the
generated denotation and exhaustion in a bounded reference run. It is not an
error value. Generated execution has no arbitrary fuel cutoff.

The one-way building blocks are [`Refines`](../P4SpecTec/Refine/Calc.lean)
and [`StateRefines`](../P4SpecTec/Refine/StateCalc.lean).
A complete certificate additionally establishes:

- **Source and representation:** the quotation identifies the selected
  artifact; every claimed source input has a related generated representation,
  and admitted generated inputs represent that domain.
- **Environment and dependencies:** initialization succeeds, global tables
  satisfy `HoldsSpec`, and local overrides, guards and extern contracts match
  the actual invocation.
- **Observations and composition:** the representation preserves the claimed
  observations; callee contracts compose through actual intermediate states,
  including failed prefixes and ordered iteration.

The baseline relation `Rel v x := canon v = canon (toValue x)` supports
value-equality reasoning, not every observation. In particular, erasing
metadata does not by itself justify hinted-print correspondence. A theorem
conditional on `Rel` also does not prove source coverage.

Forward proofs follow reference evaluation, using fuel induction for recursive
groups and callee contracts for external calls. Reverse proofs must construct
finite executions. Generic reverse automation is a design obligation, not an
assumed consequence of the forward tactic.

### 5.2 Trusted vs checked

There are three complementary evidence levels:

1. Kernel checking and axiom audits establish valid Lean artifacts.
2. Differential tests compare both Lean execution paths against upstream on
   selected inputs under matched configurations.
3. Correspondence proofs establish the contract in section 5.1.

A universal theorem about the generator itself is deliberately outside the
selected strategy. Per-artifact checking allows the generator to
evolve without re-verifying its implementation, at the cost of producing and
checking certificates for each artifact.

Certificates remove reliance on generator and tactic correctness **relative
to the chosen reference and statement**. They do not prove the reference port,
runtime helpers, exporter or upstream frontend faithful to intended P4.
No claim about reducing trusted code size follows without measurement.
The allowed proof axioms are `propext`, `Classical.choice` and `Quot.sound`;
`sorry` and native-decision escape axioms are not acceptable certificates.
See [Certification](certification.md#what-remains-trusted) for the concrete
trust inventory.

### 5.3 Deviations forced by Lean

This register includes representation changes and deliberate comparison-profile
restrictions, not only choices imposed by Lean. Each needs compatibility with
the claimed observations; new differences require an explicit entry.

- **Syntax representation:** named inductives and ordinary constructor unions
  replace OCaml recursive tuples and polymorphic variants. Unmodeled EL hint
  syntax remains JSON; consumers must validate supported forms.
- **Control effects:** explicit fuel and error data replace unrestricted
  reference recursion and exceptions. Exhaustion never becomes a default.
- **Execution profile:** sequential, cache-free interpretation omits cache
  registration, hooks, backtraces and deterministic checking. These modes are
  not interchangeable
  when extra evaluation consumes state.
- **Diagnostics:** debug expressions evaluate without printing; traces and
  source regions are outside baseline observations.
- **State and contexts:** immutable tables, explicit environments and signed
  63-bit fresh state replace mutation, preserving the chosen 64-bit OCaml
  profile, including wraparound and failed-attempt allocations.
- **Values and equality:** structural values replace identity/hash shortcuts;
  generated equality uses runtime-value comparison. Numeric representations
  and conversions preserve signedness and checked failure behavior.
- **Text and transport:** semantic text uses bytes, identifiers use strings.
  JSON ingress rejects invalid UTF-8 and unpaired surrogates; this transport
  restriction is not a lossless encoding of every OCaml string.
- **Notes and quotations:** generated values carry static type notes;
  quotations omit regions and hints and use reducible constructors. Print
  policies and source-identity normalization require separate justification.
- **Tuples and decoding:** right-associated Lean products flatten to runtime
  tuples; genuinely nested source tuples need a distinguishing representation.
  Encoders are structural; decoders require sufficient fuel.
- **Recursion and modules:** monotone fixpoints, shared recursive-group modules,
  qualified names and keyword escaping satisfy Lean's proof/binding constraints.
  Shape inspection uses well-founded recursion rather than fallback answers.
- **Logical rules:** positive iteration witnesses meet positivity constraints;
  negative premises test executable mismatch. Logical fallback rules may
  overapproximate execution, so soundness does not imply exactness.

Temporary legacy behavior and unsupported constructs belong in
[Certification](certification.md#implementation-boundaries), not as permanent
exceptions to these requirements.

### 5.4 Per-construct encodings

| Construct | Encoding obligation |
|---|---|
| Syntax types | Inductives, structures or aliases with representation coverage |
| Clause or rule path | Ordered pattern tests, bindings and explicitly sequenced calls |
| Partial operation or downcast | The correct failure tag, never a default or fabricated divergence |
| Alternatives, negation, iteration | Preserve mismatch/error distinctions, evaluation order, length conditions and intermediate states |
| Record/list/text update | Preserve operand order and bounds behavior; reject paths without an established encoding |
| Subtype conversion | Explicit injection, partial projection and membership, retaining instantiated type arguments |
| Builtin or extern | Named primitive/interface plus an operation-specific semantic contract |
| Table | Row dispatch with initialization and lookup obligations |
| Printing | Explicit hint-policy and representation compatibility |
| Logical relation | Executable soundness; converse and determinism proved separately |

## 6. Evolution and validation

Pin source, export and toolchain identities. Recheck generation, quotation
identity, certificates and upstream observations after relevant changes.
Preserved names do not imply preserved meaning.

Tests must cover successful and rejected executions and distinguish semantic
failure from timeout, missing data and harness errors. Mutation checks should
target generated behavior, quotation identity and representation assumptions;
detecting selected mutations is not proof of detecting every bug.
Coverage reports must expose unsupported cases and dependency exclusions.

## 7. Scale

Treat generation, elaboration, proof checking, memory use and runtime
execution as different costs. Separate proof modules and explicit dependency
groups support targeted rebuilding, but actual parallelism depends on the
import graph, not merely on splitting files.

Optimize measured bottlenecks without weakening statements or axiom audits.
Sharing lemmas and reducing unnecessary dependencies are preferable to masking
failed obligations with resource increases. [Performance](performance.md)
owns measurement methods and results; no runtime speedup is assumed.

## 8. Downstream acceptance

A useful example must connect a source domain, actual environment, dependency
closure and observations to a client theorem. A property over convenient
generated values alone is insufficient. Include representable negative inputs
when rejection is part of the claimed semantics.

Consumer proofs guide reusable interfaces without determining the reference
semantics. Equivalence of another proof-friendly P4 model is a separate
downstream theorem, not a consequence of this compiler's certificates.

## 9. Alternatives and tradeoffs

AL rather than IL or SL keeps execution and rule structure at one boundary
(section 3). Per-artifact rather than universal compiler verification favors
generator evolution but incurs repeated proof-checking costs (section 5.2).
Uniform state avoids effect-analysis obligations but can make pure-looking
operations carry state.

An interpreter-only library is simpler; the generated interface must justify
its additional machinery through usable proofs and acceptable checking cost.
A different frontend, verified effect analysis or optimizing translation is
worth reconsidering when a concrete benefit supports its new preservation
obligations. These are engineering choices, not novelty or superiority claims;
see [Related Work](related-work.md).

## 10. Open questions

The main unresolved design problems are generic reverse realization,
compositional contracts for printing/externs/packets, automated representation
coverage, a stable client proof API, and certificate granularity at full scale.
Logical determinism also requires rule-overlap arguments, not merely ordered
execution.

A solution must preserve the correctness contract, identify changed trust
assumptions and supply evidence for claimed usability or performance.
Implementation schedules and milestone progress are intentionally maintained
outside this document.
