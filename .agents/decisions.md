# Decisions

Current cross-cutting choices and reasons. Updated 2026-09-27.
Rules belong in [AGENTS.md](../AGENTS.md), architecture in
[Design](../docs/design.md), and detailed constraints in the linked topic
notes. This register is not a chronological log.

## Scope and product (2026-09-26)

Keep AL as input, the handwritten Lean AL reference, and the generated model.
The bounded field-update consumer is complete; broader M3 is incomplete and
paused. The earlier blanket authorization to complete M3 is superseded by the
user's pause and subsequent bounded requests. New feature work needs a newly
agreed scope. Reason: demonstrate a complete usable source connection without
mistaking isolated generated/proof fixtures for full-P4 support.

The next major milestone is complete Nano-P4 support and certification, with
core semantics and target composition as separate required acceptance stages.
[Design section 9](../docs/design.md#9-nano-p4-scope-and-acceptance) owns the
scope and definition of done. Reason: demonstrate the full architecture on a
bounded language before expanding production full-P4 support. The user
first authorized settling this scope and then explicitly approved autonomous
implementation of the Nano plan, then explicitly requested completion through N2,
then on 2026-09-27 approved starting N3 at its first checkpoint. N4–N6 remain
planned; broader full-P4 M3 remains paused. Use the model tiers in
AGENTS (small for bounded inventories, mid-tier for bounded implementation/tests,
strongest for difficult semantics/proofs and independent review), with explicit
ownership and one integrator. Confidence high in the milestone choice;
N1 settled reverse-proof and runtime-representation feasibility. Broader core
coverage and concrete target composition still determine the remaining schedule.
Revisit scope only through an explicit design
decision, not by excluding difficult cases from coverage.

The goal is a certifying compiler, technically a proof-producing semantics
translation, not a universally verified generator. Reusable models amortize
per-artifact checking and allow generator evolution. This is a tradeoff, not
a claim of general superiority over verified compilation.
[Discussion](notes/compiler-certification.md) retains the user-requested
rationale; [Related Work](../docs/related-work.md) owns sources.
Confidence high; revisit with measured scale or consumer evidence.

## Pins and reproducibility (2026-09-25)

P4-SpecTec is pinned at `8c8e0c6f` on `gsoc-nano-spec`, because Nano is
not yet on the chosen upstream main baseline. Its companion Nano spec is
`60dfd991`. A separate submodule avoids upstream's nested SSH checkout.
Return to upstream main when Nano lands there; possible branch rebasing
makes provenance checks important. Toolchain identities remain in pin files,
not a second manually maintained version list.

Nix owns the environment; elan supplies Lean, with Batteries pinned alongside
it and no Mathlib selected. Source-preserving compressed snapshots avoid huge
generated inputs in Git. Specific tradeoffs and revisit points are in
[translation choices](notes/translation-design.md#build-and-storage-rationale).

## Code ownership and placement (2026-09-26)

Use one Lake package, with libraries for concrete artifact/build boundaries and
module directories for ordinary internal organization. Empty planned libraries
do not belong in the build. Preserve mirror/generated provenance; mirror Lean
unit-test ownership in the test namespace and colocate cross-language oracle
suites. Share harness plumbing without sharing independent semantic oracles.
Remove tests by duplicated obligation, not by count. Reason: clear extension
points and less navigation/maintenance without weakening certification.
Confidence high; revisit a library boundary when implemented code needs an
independent artifact or build policy. The completed refactor is `ad1ac33`;
[maintenance evidence](notes/repository-stewardship.md) records review and checks.
Configuration/import ordering follows the same ownership principle: preserve
semantic and upstream order, group by purpose, alphabetize equivalent peers.
Reason: predictable extension points without a new sorting framework.

## Interface and correctness (2026-09-26)

Use `ExampleProofs/NanoP4FieldUpdate/` for the downstream example, with tests
beside proofs. The rename deliberately has no old-namespace compatibility shim.
Provided libraries remain usable without examples; reusable proof support
stays in `P4SpecTec.Refine`. Reason: make library versus consumer boundaries
visible and checked. Revisit if another client needs a stable wrapper API.

The target is two-way terminating correspondence on a declared source domain,
including relevant failures and state, not just relation run-soundness.
Generated certificates cover both directions for a bounded fragment. Initialization,
source/representation adequacy and observation contracts are separate
obligations. [Translation choices](notes/translation-design.md) preserve
implementation rationale and uncertainties without duplicating architecture.
[Field-update evidence](notes/field-update.md) records the completed consumer.

For the current Nano pin, printing requires an explicit empty hint environment.
A reusable theorem now proves canonical equality preserves no-hint output and
errors, and the quote checker independently checks decoded/compiled emptiness.
Reason: this is the actual Nano policy table; the broader provenance invariant
is needed only for hinted specifications. Confidence high. Revisit on any pin
or policy change; do not generalize the empty-table result to hinted printing.
The raw-extern obstruction motivates the runtime-only carrier choice below;
PACKET rewrapping changes the actual subsequent callee result and remains forbidden.

These topic constraints remain binding when their work resumes:

- [State integration](notes/state-integration/overview.md): allocation survives
  rejected attempts; bounded fixtures are not production integration.
- [Byte text](notes/byte-text.md), [type runtime](notes/type-runtime.md) and
  [print hints](notes/print-hints.md): checked semantic boundaries, no fallback
  success on unsupported values or exhaustion.
- [Full P4](notes/full-p4/overview.md) and its [corpus](notes/full-p4/corpus.md):
  emission census is not compilation; exact identities and retained failures
  constrain coverage claims.
- [Nano target](notes/nano-target.md): preserve raw ExternV and shared verify
  ABI mismatches; do not invent typed target or boot/STF coverage.

## Nominal codec dictionary binding (2026-09-27)

Generated closed nominal fields bind their source declaration's encoder and
decoder with explicit parameter dictionaries. Primitive and list/option fields use the same
explicit selection recursively. Local source type parameters shadow global
names. Reducible Lean aliases must not let unrelated later instances change a
field's codec or add accidental fuel layers. Production recursive syntax exposed
opaque encoder alias capture in initializer/selectCase fields; explicit source
encoder binding removes that accidental instance dependency. A declared alias retains one
frame; its old incidental minimum fuel is not preserved. Contextual tuples now have exact empty/two-field codecs with explicit dictionaries;
closed right products that would flatten and unsupported arities fail closed.
Function-type dictionaries remain unchanged pending separate support.
Confidence: high, supported by hostile-instance and bound-name regressions and
actual source-codec proofs. Revisit when tuple/function field support expands.

## Declared source extern domains (2026-09-27)

Opaque source declarations use the independent `ExternV` shape with arbitrary
JSON, matching pinned upstream `runtime/value/match.ml` and the checked Lean
membership rule. `Source.Valid.external` still requires an actual external
source declaration. Generated source codecs share this domain consistently;
using `False` would incorrectly remove `objectState` and the PACKET alternative
from the full Nano source domain. The separate runtime-only `value` alternative
remains excluded from source admission. Opaque fields bind canonical extern
encoder/decoder dictionaries explicitly, including under reducible aliases.

Confidence: high; checked membership equivalence, actual objectState codec,
raw-extern rejection for the defined value family and hostile-instance regressions
pass. Revisit if upstream changes opaque type membership. Additional target-state
invariants remain target contracts, not an unrecorded restriction of core syntax.

## Nano runtime representation (2026-09-26)

Preserve extract's raw `ExternV` result through an explicitly configured
runtime-only alternative in the generated `value` carrier. Keep source AL
quotations, `packetValue` and `objectValue` unchanged; do not wrap the result in
PACKET. Follow the actual supplied subtype-check mode: SkipSC remains true,
MixopSC matches source constructors, and unsupported extension-sensitive checks
reject generation. Same-static-type casts preserve the raw value.

Reason: the pinned guard-free semantics writes this value into the receiver;
changing its shape would repair upstream behavior and change subsequent calls.
The chosen interface uses ordinary codecs and contextual contracts, with exact
callback/state evidence separate from full target certification. Confidence high
for this Nano profile. Revisit if a pin changes the callback result, subtype-check
forms, or a new carrier needs a different runtime extension. N2 supplies all 162
source codecs and the selected closure's call invariants; broader core coverage
remains N3 and complete target composition remains N4.

## Runtime-inclusive evaluation domain (2026-09-28)

`Source.Valid` takes a domain with two parts: the opaque external-type domain and the
runtime-only alternatives of declared types. The source profile (`externDomain`) has
none, so its grammar, codecs and statements are unchanged. The runtime profile
(`runtimeDomain ["value"]`, from `--runtime-extern value`) admits exactly a raw
`ExternV` at `value`, the shape extract writes into a receiver. Evaluation-side domain
claims (entry, producer, call admission) are stated over the runtime profile for
callables whose domain involves the `value` closure. Reason: after an extern callback
the actual contexts hold raw extern values, so source-domain preservation is false for
the evaluation relations; a runtime profile states the actual domain without assuming
the target avoids raw values, which NanoSwitch does not. Types whose declared closure
avoids `value` have the same values in both profiles (`Valid.runtimeIff`, from one
checked closure certificate), so their source codecs lift. Alternatives rejected: a
carrier-image domain (vacuous), a separate `RuntimeValid` inductive (duplicates every
grammar lemma), owning the obligation in N4 (the core call closure does not depend on
the target). Confidence medium-high; revisit if a pin changes the callback result
shape or another carrier needs a runtime alternative.

## N3 certificate shape (2026-09-28)

Generated relations try complete rule-path attempts in the reference's flattened order:
each attempt repeats its group's input match and shared premises, as
`invoke_defined_rel` flattens the paths of all groups into one sequence. The earlier
shared-prefix form was observationally equal but needed distribution through
destructuring matches in every proof. Reason: correct by construction; alternatives pair
one to one. Cost: shared premises run once per attempted path, as upstream does.
Revisit only with a proved distribution lemma for every prefix form.

Certificates of definitions whose callable closure reaches an extern relation quantify
the generated `Externs` instance and assume `externsContract cfg`: on related inputs,
every configured callback outcome has a related generated outcome and conversely, with
failure kinds preserved. The extern relation's invocation certificates follow from it,
and the completion manifest binds the `extern` obligation to their combined claim. The
concrete NanoSwitch target discharges the contract in N4. Reason: design section 9.2
allows extern-dependent results under explicit contracts; one contract keeps every
caller's assumption identical. Revisit when the target exposes output invariants a
caller needs.

A certificate module keeps the 4M heartbeat default; a group theorem adds 1M per source
rule path or clause of its members. Symbolic execution cost grows with the paths
explored; a fixed budget either fails large definitions (`bin_op`, 26 clauses) or leaves
small ones loose. The budget is a resource limit, not a weakened statement. Revisit
with measurements or if a budget masks a runaway tactic.

Generated `#audit_axioms` commands sit at the end of their namespace or section (ahead
of any `mutual` block), not after each theorem (`Emit.hoistAudits`, 2026-09-28, validated
in `770e405`). An audit waits for its theorem's proof, so placed after it, it serialized a
module's proofs, which Lean otherwise elaborates in parallel. The audits and their exact
axiom rule are unchanged. Tools that pair audits with theorems (`replay-cert.py`, the
field-update mutation runner) must follow this layout. Revisit if Lean exposes
per-declaration async audits.

Forward and reverse certificates now have independent per-group dependency chains,
with the old module names retained as import-only aggregates. This lets a caller
wait on its own direction and keeps reverse-tactic edits out of forward-only
modules where no shared extern dependency reintroduces them. Statements, SCC
boundaries and audits are unchanged. Replay expands aggregate names to the actual
proof sources; timing an aggregate import alone does not measure proof work.

`scripts/nano-certification.py --require-owned N3` requires every core-stage obligation
owned by N0–N3. Core replay of the typing corpus is owned by N4 and printing
observations are target-stage; they stay reported, not waived. Source identity is
discharged by the completion CLI's own checks (pins, export digest, generated freshness,
`check-quotes`, `check-coverage`), recorded as `checkedBy`, never as a compiled claim.

## Knowledge ownership (2026-09-26)

README is the short introduction/status; Design describes the intended system;
Certification records delivered guarantees; Performance owns measurement
interpretation with dated snapshots; Related Work owns literature synthesis.
Checked walkthroughs stay beside examples. Reason: readers should not reconcile
competing copies of the same claim.

The approved `.agents/` organization is a small current-state entry point,
this cross-cutting rationale register, deferred work in Roadmap, and working
knowledge grouped by topic. Plans, experiments and reviews belong together.
Start with one note; use a topic directory only for independently useful
supporting material. Git history is the archive, without new archive folders,
tags or an accumulating lessons journal.

Keep `tend-repo` versioned here and instruction-only until observed use
justifies automation. It applies AGENTS policy, preserves open obligations
during compaction and improves from evidence, including removing ineffective
guidance. Revisit packaging if another repository needs it.

## Workflow and recovery (2026-09-26)

Direct commits are the default because this is currently a personal project;
feature branches are optional isolation, PRs require explicit request.
The user explicitly changed routine CI to asynchronous feedback after slow
remote gates blocked iteration. Local validation and independent review remain
pre-push checks; documentation-only work reuses unchanged code validation.
AGENTS owns the rules for pending runs, failed CI and final release/PR checks.
Reason: preserve verification while removing a serial wait from every turn and
avoiding repeated full builds for evidence-only updates. Confidence high in the
workflow split; revisit if failures remain unattended or collaboration/protections
require stronger pre-merge coordination.

Historical experiments were retired, not integrated or declared correct.
The user chose a small committed-history bundle over the 24 GiB checkout
snapshot. Ignored campaign data and exact checkout metadata were discarded;
the bundle cannot restore exact corpus execution. Recovery boundaries,
identities and the failed casting experiment remain in
[archive recovery](notes/archive.md). Removing that local-only backup is not
part of routine compaction.
