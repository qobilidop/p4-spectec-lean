# Nano-P4 certification implementation plan

Active implementation plan, 2026-09-26. The user approved autonomous execution
after the planning checkpoint, starting with N0/N1. The contract is
[Design section 9](../../docs/design.md#9-nano-p4-scope-and-acceptance), not this
work breakdown. Both core semantics and target composition must close.
Broader full-P4 M3 remains paused.

## Baseline and critical path

Scope revision: `da631a9988298bb8705f2e9d0df3306092454f40`. Current coverage
contains 76 functions, 77 relations, 26 builtins and one extern relation.
There are 18 forward AL certificates, 77 relation run-soundness theorems and
two logical determinism theorems. Generated reverse coverage is absent;
the handwritten field-update example proves a bounded two-way connection.
These are inventories, not percentages of language behavior certified.

The following closures were recomputed from `NanoP4Spec/coverage.json`, following
both direct dependencies and recursive-group membership, counting the root:

| Entry | Bodied definitions | Builtins | Extern relations |
|---|---:|---:|---:|
| `Var_init` | 5 | 1 | 0 |
| `Program_load` | 14 | 3 | 0 |
| `Expr_eval` | 7 | 10 | 0 |
| `Program_ok` | 83 | 8 | 0 |
| `NanoSwitch_init` | 94 | 8 | 0 |
| `NanoSwitch_drive` | 66 | 12 | 1 |

Closures overlap and exclude representation/initialization obligations, so
their sizes are prioritization evidence, not effort estimates. The smallest
recursive relation dependency closure is the `Type_eq` / `ParameterType_eq` group. Its
reported subtype-check blocker is the first syntactic exclusion, not a
complete list of proof obligations; removing it can expose further work.

The critical path is: complete obligation inventory; reusable reverse and
relation proofs; representation and primitive contracts; full core coverage;
target composition; whole-program evidence and release check. Investigate
target representation and printing at the start, in parallel with proof
feasibility, because either can change the representation contract.

## N0. Inventory every completion obligation

Deliver a versioned, machine-readable Nano completion manifest and a checker
mode that reports outstanding obligations without claiming completion.
Extend the existing coverage machinery rather than creating a competing list
of callable names. Include all source types, initialization declarations,
source-domain predicates, representations, both proof directions, builtin and
extern contracts, observations, corpus identities, and consumer evidence.
Record exact source/export identities and stable links to checked declarations.

Generate the callable/dependency/SCC census from the decoded export; review
source-domain and observation requirements independently of emitter eligibility.
Inventory all pinned corpus cases, including typing failures and STF sessions,
with explicit source-derived reasons for any out-of-profile case. An emitter
blocker or unsupported adapter is never an out-of-profile reason.

Add a strict completion mode now. It must fail on the current incomplete
manifest, while ordinary CI can check freshness, verified claims and the
expected outstanding obligations. At N6 the strict mode becomes a required
passing gate. Missing directions/contracts/types must not be accepted through
an arbitrary theorem name or an unchecked metadata flag.

Exit: every design requirement has an owner, expected proof/evidence shape,
dependency links and a reproducible check; mutation tests reject a removed
obligation, forged declaration, stale source identity and hidden corpus case.
No implementation difficulty has been removed from scope.

Primary surfaces: `Codegen/Coverage.lean`, `Codegen/Coverage/Check.lean`,
generated coverage metadata and the existing quotation/corpus checks.
Paths under `Codegen/` and `Refine/` below are relative to `P4SpecTec/`.

## N1. Resolve the feasibility questions before broad expansion

Run three bounded workstreams after N0 establishes their obligations:

1. **Reverse execution and relations.** Generalize finite reference witnesses
   from the field-update example into reusable support. Establish stability
   under increasing sufficient fuel so sequential calls and failed alternatives
   can share a finite bound. Cover bind, ordered choice, hard error, mismatch,
   optional execution and ordered iteration. Exercise a recursive generated
   function, then `Type_eq` / `ParameterType_eq` using actual Nano definitions.
   Connect terminating `partial_fixpoint` outcomes to finite reference runs;
   do not infer reverse correspondence from forward soundness or determinism.
   Decide whether relation correspondence can use executable callee contracts
   directly, avoiding blanket logical-determinism obligations.
2. **Target representation.** Reproduce the raw `ExternV` extract result through
   the actual AL callback and a subsequent receiver use. Propose a faithful
   representation/adapter and prove its contextual obligation on this path,
   including failure. A `PACKET` rewrap is not an acceptable repair. Prefer a
   faithful local representation solution; use a corrected upstream pin only
   if a concrete correction is available and reviewed. Keep pin changes in a
   separate regeneration/revalidation step. Classify the shared verify ABI
   mismatch from actual Nano call sites, not successful direct-helper tests.
3. **Observation adequacy.** State the extra provenance and hint-environment
   invariant needed for `print_` byte results, beyond canonical `Rel`. Check
   that the proposed representation admits source constructors and preserves
   intermediate values as well as output bytes. Separate this pure text-return
   builtin from interpreter debug output, which is outside the profile.

Exit: audited small proofs or explicit counterexamples for all three
workstreams, an agreed representation and certificate interface, and measured
elaboration/proof cost. Include reachable mismatch and hard-error branches;
synthetic fixtures may isolate mechanics but cannot replace the real Nano
recursive relation and callback probes. Do not launch broad proof generation
while a chosen interface has an unresolved counterexample.

Primary surfaces: `Refine/Calc.lean`, `Refine/Value.lean`, `Tactic/Refine.lean`,
`Codegen/Validate.lean`, `ExampleProofs/NanoP4FieldUpdate/Correspondence.lean`,
and the existing Nano target/print ports and tests. Retained constraints:
[Nano target](nano-target.md), [print hints](print-hints.md),
[translation choices](translation-design.md).

## N2. Build reusable representation and primitive contracts

Implement the interfaces selected in N1, with independently stated source
domains, representation coverage, admitted generated-input validity and
decoder sufficiency. Handle recursive/nested syntax and value families,
polymorphic instantiations, subtype injection/projection and membership.
Prove the invariants at initialization and preserve them at every call;
do not add hypotheses that no actual caller can establish.

Complete builtin contracts by family: lists/maps/sets and byte text;
numeric/bit operations; hint-sensitive printing. Cover all 26 builtin
declarations, including those unused by the selected execution examples.
Include operation-specific rejection/error behavior and legal parameter
instances. Generate and audit the wrappers' connections to reference dispatch.

Extend both proof directions together for type arguments, casts, indexing,
slicing, updates, membership and iteration as demanded by the inventory.
Implement ordered relation attempts, negative premises and recursive groups
without requiring every logical relation to have an exact converse. Preserve
the existing run-soundness layer and prove determinism only where a chosen
proof or client actually needs it.

Exit: generated two-way certificates for the original 18 functions on their
full declared domains, the N1 recursive relation group, and the `Var_init`
closure (`default`, `add_var_e`, `dom_map`, `in_set`, builtin `add_map`).
Use `Type_ok` as an intermediate builtin/lookup integration check: its closure
is `Type_ok`, `typeIR_of_typeDefIR`, `find_typeDef_t`, and builtin `find_map`.
These are integration checks, not a reason to omit other N2 obligations.
Reusable support stays outside `ExampleProofs`; no generated files are patched
by hand. Record remaining inventory blockers and current proof costs.

Primary surfaces: `Codegen/Types.lean`, `Codegen/Funcs.lean`,
`Codegen/Validate.lean`, `Codegen/Emit.lean`, `Refine/`, `Tactic/`, and
`P4SpecTecTest/`. Reachable legacy matching/substitution fallbacks must be
replaced or proved unreachable on the admitted domains before certifying them.

## N3. Close core semantics in dependency order

Use these actual entry points as integration checkpoints, while scheduling
their helpers and SCCs in dependency order:

1. `Program_load` and `Expr_eval`: independently useful loading and expression
   closures, with success and representable rejection/error results.
2. `Program_ok`: all typing relations, including syntactically valid programs
   rejected by typing; do not assume well-typedness to certify the checker.
3. `NanoSwitch_init`: compose typing, loading and evaluation-context creation
   from exported programs, discharging actual environment assumptions.
4. `NanoSwitch_drive`: certify parser/control behavior and the six-member
   call/table/statement recursive group under explicit extern contracts.
5. Sweep every remaining exported definition and representation, including
   stdlib helpers outside these entry-point closures.

Exit: both directions for all 153 bodied definitions at the current pin,
all 26 builtin contracts, representation/initialization evidence, and all
77 relation run-soundness theorems; regenerate the denominator on pin changes.
The core completion check passes, with target-dependent results explicitly
conditional on the named extern contracts. No missing callee or SCC member
can be hidden by a conditional wrapper theorem.

## N4. Discharge target contracts and compose packet execution

After N1 settles representation, target port work can proceed alongside N2/N3.
Complete the typed Nano extern instance, packet operations, driver and semantic
target initialization using the pinned upstream NanoSwitch as the oracle.
Prove the contracts consumed by the core, including intermediate contexts,
callback order, failures, fresh counters where used, and subsequent packets.
Choose effects based on actual Nano requirements; do not reopen production
full-P4 state integration merely because stateful test fixtures exist.

Provide a documented runner accepting exported programs and packet/test data.
Keep parsing/STF syntax upstream; make Lean perform semantic initialization
and loading. Compare the generated path, Lean reference path and pinned
upstream outcomes over the full applicable corpus. Preserve ordered packet
bytes/ports and forwarding/drop results as well as persistent state.

Exit: core extern assumptions are discharged for the concrete Nano target;
initialization through packet processing has a checked two-way composition
theorem. Every applicable corpus case matches the oracle; timeouts, missing
data, harness errors and unsupported cases remain blockers. The strict target
check passes without manufacturing success from a representation failure.

Primary surfaces: `P4SpecTec/BackendSim/NanoSwitch/`, generated `Externs`,
`test/nano-target/`, `test/nano-verify/`, `test/diff/` and colocated runner tests.
Historical target constraints remain in [nano-target.md](nano-target.md).

## N5. Demonstrate a whole-program theorem

Select the program and property during N0; build the proof alongside N3/N4.
Use a small Nano parser/control filter whose packet-field test determines
forward versus drop, with actual extraction so target representation is
exercised. Prefer an existing pinned source example if it expresses this
property; otherwise add a minimal source fixture with upstream observations.

Prove the exact port/payload outcome for a stated family of valid packets and
a rejection/drop family, starting from the exported program and real semantic
initialization. Include the composed reference statement, not merely a theorem
about generated values. If packet contents are unmodified upstream, state that
fact rather than inventing an output-rewriting example. Keep intermediate and
sequential-call evidence so discarded receiver corruption cannot pass unnoticed.

Exit: a checked consumer certificate with a walkthrough and distinguishing
mutations of source identity, packet branch, extern result and output/state.
The proof must consume library contracts; it cannot duplicate a handwritten
semantics or silently assume the missing target/initialization obligations.

## N6. Close release evidence

Make strict combined completion a required passing part of `scripts/check.sh`.
Audit the final manifest against the source, signatures and design criteria;
verify scope has not narrowed during implementation. Keep partial-coverage
diagnostics useful for later specifications without weakening Nano's gate.
Add cross-layer mutations for alternative ordering, hard-error retry, omitted
constructors, wrong quotations, incompatible print provenance and corrupted
target state. Identify which check rejects each mutation.

Record generation, elaboration/proof checking and replay costs separately.
Resolve unexplained scaling regressions without weakening statements, domains
or axiom audits. Update the certification guide and README only to the claims
actually delivered. Independent review, the full local gate and exact-revision
remote CI must pass before declaring the milestone complete.

## Execution and estimation

Implement each step as small reviewed, validated commits. Every checkpoint
records the exact covered closures, still-open obligations and next step in
status; follow AGENTS for review, publication and generated-artifact handling.
Proof, target and inventory work may use separate writers/worktrees, but shared
representation and certificate interfaces must be agreed before concurrent
edits to emitters. One integrator owns generation and final gate evidence.

No reliable calendar estimate is available before N1. Estimate the rest after
measuring the recursive relation proof, target adapter and first full closure;
definition counts alone are misleading. A failed feasibility probe triggers a
revised implementation design and explicit remaining obligations, not reduced
scope or a milestone-completion claim.

Immediate implementation increment: N0, then the three bounded N1 probes.
Autonomous execution is now authorized; preserve scope and the trust boundary.

## Active N0/N1 findings

- Luna inventory confirms 350 AL declarations: 161 defined types, one external
  type, eight variables and the 180 callables already in coverage metadata.
  Corpus: 78 P4 source files and 39 STF sessions. The existing
  `positive/src-addr-filter` is the candidate N5 extraction/forward/drop program.
- Astra reverse feasibility investigation found no general outer-fuel stability
  lemma. Generated `partial_correctness` and mutual variants can support finite
  reverse-witness motives without total termination. The reference subtype path
  has a fixed internal fuel 1000; test whether it prevents full-domain reverse
  correspondence before expanding proofs. Do not silently bound source nesting.
- N0 implementation uses the existing compiled coverage checker as the source
  of callable proof evidence. A Nano-specific completion inventory adds all
  declarations, source/domain/initialization/observation obligations and corpus
  references; missing proof interfaces stay unresolved. JSON cannot mark an
  obligation checked. Root owns integration; Sol owns corpus inventory/checks.

## N0 implementation checkpoint

The source-complete inventory is `NanoP4Spec/completion.json`, regenerated by
`scripts/nano-certification.py`. It joins the existing callable checker to all
350 declarations and 888 obligations. The 95 bindings are existing forward and
run-soundness evidence; 793 obligations remain unresolved. Contract kinds without
statement/checker adapters cannot be marked complete. Dependencies conservatively
combine callable/SCC edges, named types and profile prerequisites; this is
structural accounting, not a proof of semantic dependencies.

Sol's pinned corpus inventory covers 78 P4 programs and 39 STF sessions. All
78 typing observations exist (48 pass, 30 AL typing failures, including all
21 negative programs); only three guard-disabled STF observation sets exist.
All 117 replay obligations remain open pending checked completion adapters.
The N5 candidate is pinned `positive/src-addr-filter`: actual header extraction,
source-address acceptance for 1/2, default drop, and distinguishing packet cases.

Independent read-only AI-agent review: Astra `/root/review_nano_plan`.
Original findings were inconsistent HEAD/index pin selection, insufficient
representation dependency links, and an intermediate corpus-ID prefix mismatch.
All were resolved, with staged-gitlink and source-type mutation coverage.
The final review found no remaining blocking issue. Reviewed blobs:

| File | Blob |
|---|---|
| `scripts/nano-certification.py` | `16aab0d00b092d227e6b5db15f2a82a7eb5de43a` |
| `NanoP4Spec/completion.json` | `ebcbc04996ef5aab4fbca2eddbbba07c8df9bb78` |
| `test/completion/test_completion.py` | `0ff6aa274b9341180ded95a65ac9d2038a5687fb` |
| `test/nano-certification/corpus.py` | `7a55d63dd064acef93604f51955befeca3c64ec4` |
| `test/nano-certification/test_corpus.py` | `d8aa6ef72b316522ff26e034353713a89566ed7b` |
| `test/nano-certification/corpus.json` | `bfdd42923e6836df02652f653cc88bc262a25323` |
| `test/nano-certification/README.md` | `64528f094882961d3c2007cd98a263e05f6e81a4` |
| `scripts/check.sh` | `71f8ab201191d553bc7ab0d7c90406b371cafcf5` |
| `docs/certification.md` | `e76519e325c33c7a96cf6b427b8ab4b6f4df500d` |

Author and reviewer independently ran the 15 completion tests, 19 corpus tests,
and ordinary checker successfully. Strict all/core checks correctly exit 1;
core reports 746 unresolved obligations. Review did not recapture upstream,
prove contract feasibility, review N1 proofs, or supply a full-gate/remote verdict.
Root's full `nix develop -c /Users/qobilidop/my/work/p4-spectec-lean/scripts/check.sh`
passed with actual exit 0, no skips (session 77137,
`.artifacts/nano-n0-realize-gate.log`), including the pending reverse calculus.
Final evidence text receives text/whitespace checks. Remote CI remains pending.

## N1 reverse calculus checkpoint

`Refine/Realize.lean` introduces `EventuallyRuns` (one outcome at every
sufficiently large fuel) and `Realizes` (each terminating generated outcome
has a related eventual reference witness). This entails the design's finite
existential witness and supports a common fuel bound for sibling computations.
It does not assume interpreter fuel monotonicity. Rules cover fixed overhead,
bind, ordered alternatives, negation and ordered list traversal, including
mismatch, hard errors and a failing prefix before a diverging later element.

Author: Astra `/root/review_nano_scope`. Independent read-only review: root
Astra, who inspected all statements, proofs and fixtures after authorship.
No findings. Reviewed library blob `28a9cc8e3a55aa548366321c3888a2898a841acb`;
test blob `f4e6936f0c8eee80c66cc3704820b2a555494294`.
Sixteen library theorems and fifteen named test theorems carry exact axiom
audits. Root wired the library/test root imports and independently ran
`nix develop -c lake build --wfail P4SpecTec.Refine.Realize P4SpecTecTest.Realize`
(exit 0, session 94233). The full N0/N1 gate above includes these modules and
passed. This review certifies neither an actual Nano reverse theorem nor
stateful/printing correspondence; the actual recursive proof remains active.

Fuel investigation, bounded scratch evidence: under `guard=true`, nested Nano
parenthesized expressions at depths 1000/1100 exhaust the internal match fuel
1000 and succeed at 2000. This is outside the agreed guard-disabled profile.
Under `guard=false`, actual quoted `repeat_` succeeded in all 24 runs with type
nesting 0/999/1000/1100, repeat counts 0/1/3, and outer fuel 512/2000. Its recursive
type argument is bare `X`, so substitution returns the replacement directly.
All five recursive subtype checks in decoded Nano target primitive Nat; the
other 209 checks are outer-constructor checks. These observations found no
in-profile counterexample and do not establish general fuel safety. Scratch
probes remain uncommitted while the corresponding proof obligation is open.

Target analysis confirms that all generated `value` encodings are outer
`CaseV`, whereas successful extract returns bare `ExternV`; canonicalization
preserves that distinction. A runtime-only raw-extern `value` constructor is a
candidate, not an adopted solution. It would need encoding/decoding and source
membership distinctions, plus audits of same-static-type subtype shortcuts,
ignored subchecks and constructor refutability. It must propagate through
`Copy_out` and `Lvalue_write` to actual receiver reuse. It must not broaden
source `packetValue`/`objectValue` or repair the value with a `PACKET` wrapper.
The concrete continuation and printing probes are still active.

## Plan review and validation

The plan is grounded in the current generated dependency graph, retained target
and print constraints, and a read-only proof-infrastructure investigation by
`/root/review_nano_scope` (contributor, not the independent plan reviewer).

Independent read-only AI-agent review by `/root/review_nano_plan` found no
blocking scope or dependency issue. It independently recomputed the baseline
counts, all six entry-point closures and the `Type_ok` closure. Its minor
wording suggestion to distinguish dependency-closure size from SCC size was
applied. Follow-up review confirmed the final plan and roadmap/status/AGENTS
routing with no new findings. Reviewed plan blob before this evidence footer:
`1c03a507e897776f2f3e9ae2d64f465cb328d173`, based on scope commit `da631a9`.
Review did not execute proofs, test feasibility or recapture upstream behavior.

Author checks: relative link targets in all four checkpoint files exist.
Full `nix develop -c /Users/qobilidop/my/work/p4-spectec-lean/scripts/check.sh`
passed with actual exit 0, no skips (session 18516,
`.artifacts/nano-plan-gate.log`). Final evidence edits receive text/whitespace
checks afterward. No new implementation or theorem is claimed; publication CI
must be checked against the plan commit's exact SHA.
