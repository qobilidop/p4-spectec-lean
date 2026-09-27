# Nano-P4 certification implementation plan

Active implementation plan, 2026-09-26. The user approved autonomous execution
after the planning checkpoint, starting with N0/N1. The contract is
[Design section 9](../../docs/design.md#9-nano-p4-scope-and-acceptance), not this
work breakdown. Both core semantics and target composition must close.
Broader full-P4 M3 remains paused. The user explicitly resumed implementation
after organization/performance work and authorized completion of N1. Root owns
integration, Astra reverse proofs and target representation, and Sol observation
composition; broad proof generation remains blocked until N1's exit criteria close.

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
`Codegen/Certificates/Forward.lean`, `ExampleProofs/NanoP4FieldUpdate/Correspondence.lean`,
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
`Codegen/Certificates/Forward.lean`, `Codegen/Emit.lean`, `Refine/`, `Tactic/`, and
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
`P4SpecTecTest/Oracle/NanoSwitch/` and `P4SpecTecTest/Oracle/Nano/Replay/` and colocated runner tests.
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

## Early N0/N1 findings (historical)

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
The final review found no remaining blocking issue. Paths and commands in the
checkpoint evidence below are historical at their recorded revisions; the
organization refactor `ad1ac33` moved tests and CLI roots without changing these
original review identities. Current tests live under `P4SpecTecTest/`, oracle
suites under `P4SpecTecTest/Oracle/`, and infrastructure tests under `scripts/`.
Reviewed blobs:

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
Final evidence text received text/whitespace checks. Inventory commit `35bda29`
and reverse-foundation commit `f6d1b05` are published; exact-head
[CI run 36276724234](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36276724234)
succeeded. This publication obligation is closed.

## N1 reverse calculus checkpoint (`f6d1b05`, historical)

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

Fuel investigation, bounded scratch evidence: direct recursive membership checks
used by dynamic guards, via `Match.sub_checked`, exhaust budget 1000 on nested
Nano parenthesized expressions at depths 1000/1100 and succeed at budget 2000.
This did not run configured guarded interpretation or change its internal fuel.
The agreed profile disables guards. Under `guard=false`, actual quoted `repeat_`
succeeded in all 24 runs with type
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
The checked continuation and printing results are recorded below; a faithful
representation and its contextual contract remain open.

## N1 target and printing checkpoint (`9309e26`, historical)

Actual quoted `Callee_eval`/`Call_eval` now run in the existing packet checker
from its checked free-pass context, with source callbacks and guards disabled.
For both 8-bit and 24-bit packets, extract succeeds and stores raw `ExternV`.
The short packet retains idx 0 and the default header; the full packet reaches
idx 24 and copies out drop=true, packetType=127, src=dst=255. Packet bits/length
and all fresh counters are checked. Subsequent callee selection returns
`unmatch`; direct extern dispatch on that receiver returns a hard error.
A deliberately isolated PACKET-rewrap mutation restores successful callee
selection, so silently repairing the receiver cannot pass this probe.

The two kernel theorems in `P4SpecTecTest/Refine/NanoTargetRepresentation.lean` prove
that no current generated `value` represents any raw extern, and no decoder
fuel can recover it. They establish the current interface obstruction, not
contextual correctness of a proposed extension. The runtime-only constructor
candidate still needs its generator/subtype audit and contextual proof.
Shared verify remains unreachable as a Nano extern-function call: Nano has
no `ExternFunctionCall_eval`; direct shared-helper success does not establish
Nano source coverage, and the retained getter-ABI failure still applies.

Nano's actual print policy table is empty. `Refine/Print.lean` proves output
and error equality under canonical equality for the empty table, including
nested unsupported values. Tests retain identifier/nonTypeName notes and
show that synthetic differing policies distinguish canonically equal values.
The quote checker independently checks decoded and compiled table emptiness;
normalized quotation equality alone would erase the needed hints. Application
requires `cfg.printHints = []`; `HoldsSpec` alone is insufficient. A general
hinted contract would additionally relate selected policies recursively.
Builtin dispatch/environment composition remains separate work.

Independent read-only reviews, with no remaining findings:

- Root reviewed Sol's packet continuation implementation and its isolated
  mutation: blob `4a3cc1970dda1b271e0f97c8ffce408c4b20c5cd`.
- Root reviewed Astra's no-hint proof and discriminating tests:
  `Refine/Print.lean` blob `51e31b7adcc715a2b8a6f7ae8efeb8534441b791`,
  `NanoPrint.lean` blob `dcb4372353f424b880852de303fc839f3822617c`.
- Astra `/root/review_nano_plan` reviewed root's raw-extern obstruction proofs
  and import: blob `a0ebe515dc851c73b9ccaca46b6b714ec1bc1e15`.
- Sol `/root/nano_corpus` reviewed root's quote prerequisite and root wiring:
  `Quote/Main.lean` blob `8dc2635471e664f560d0b002dbedd88dc150e723`,
  `P4SpecTec.lean` blob `995b13c1a8a943714545dbdd27e32c0e2f47201a`,
  `P4SpecTecTest.lean` blob `67aa0577eb4eb172c23d5e56b072841eecc52cbd`.
  These reviews do not claim upstream recapture or full target certification.
- Sol's documentation consistency review found two minor retained-note issues:
  the direct membership probe was described as guarded interpretation, and N0
  publication text was stale. Both are corrected above; follow-up review
  confirmed both resolutions with no remaining findings. No current target/print
  overclaim was found.

Focused checks, all actual exit 0: warning-failing builds of `check-nano-packet`,
`P4SpecTec.Refine.Print`, `P4SpecTecTest.NanoPrint` and
`P4SpecTecTest.NanoTargetRepresentation`; `python3 test/nano-target/check.py`;
`lake exe check-quotes` (342 matches; both tables empty). Commands ran inside
`nix develop`. The full combined
`nix develop -c /Users/qobilidop/my/work/p4-spectec-lean/scripts/check.sh`
passed with actual exit 0, no skips (session 8909,
`.artifacts/nano-n1-target-print-gate.log`). Final evidence edits receive
text/whitespace checks.
Commit `9309e268fa30125b06ea86b5cde19eeff072a3e0` is published and its exact-head
[CI 36277488013](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36277488013)
succeeded. Its implementation publication obligation is closed. No Nano
completion binding has been added, and N1's full exit criteria remain open.

## N1 recursive-proof handoff

Resolved by `7b4e0b3`; current proof and review evidence follows below. The old
unpublished draft was `efd626c7cb40004f8d6725f2b29172d09ecd8dbe` on
`wip/nano-reverse`, with artifacts under `.agents/notes/nano-reverse-proof/`.
It had checked clause bridges but no verified whole-function induction or full
gate. Its temporary worktree was removed. Historical artifact hashes, review
limits and recovery instructions remain in the pre-N1 version of this note at
`fd7ff9f`; never use that draft as release evidence.

Retained proof lessons: exclude early Q.v_eq/Q.rp_eq from broad normalization to
avoid a rewrite loop; state matched-context HoldsSpec/empty-fenv facts explicitly;
unfold only Motive for induction-hypothesis application. Explicit arithmetic
rewriting avoids expensive interpreter reduction across reassociated fuel bounds.

## Resumed N1 implementation

The user explicitly authorized completing N1 after the performance work. The
starting revision `fd7ff9f` passed exact-head CI 36286394307. This phase covers
actual recursive proof feasibility, a faithful raw-extern runtime carrier, and
printing dispatch composition; broad N2 proof generation remains outside this step.

### Optional execution and negation

Root added `Realizes.notHold` and `Realizes.optionMapM` to the existing reverse
calculus. They use actual eventual witnesses, preserve hard errors and mismatch,
and never infer fuel stability from one bounded run. Optional absence skips the
body; a present exhausted computation remains exhausted. Existing delayed fixtures
exercise the generic rules, with kernel-checked absent/error/exhaustion examples.

Independent read-only Sol `/root/organize_lean_tests` found no issues in the two-file
diff against `fd7ff9f`, SHA-256
`7d0603100a8d1e2f8688408dc39712a89640564675d1c59b658c061eab4856ea`.
Review covered proof statements/composition and unchanged contracts; builds were
integrator evidence. Focused `lake build --wfail P4SpecTec.Refine.Realize` and
`lake build --wfail P4SpecTecTest.Refine.Realize` passed (sessions 53124 and 95369),
including exact axiom audits. Full integration gate 40282 subsequently passed.

### Printing dispatch composition

Sol extended the existing unhinted congruence result through actual pure builtin
dispatch, guard-free `invoke_func` and global builtin lookup. The final theorem
applies to Nano's actual quoted `print_` declaration and generated implementation
for every related input, preserving exact encoded bytes and hard errors. The
premises explicitly require empty print hints, guard=false, no local override,
and the actual global declaration; it does not infer empty hints from HoldsSpec.
Nested values are covered by the existing generic congruence theorem. Source
and compiled empty-policy checks remain in the quotation checker.

Root independently reviewed the two-file diff against `fd7ff9f`, SHA-256
`2e44cbfc3c350bc4a76e83566cfb30abf73b878bd870ccca18a9d2965046d9e0`, against
Effects.builtinEval, invoke_func/body/builtin_func, and the generated print body.
No findings: all three fuel entries, input/output guard bypasses and hard-error
classification match the actual pure interpreter. The author's focused
`lake build --wfail P4SpecTec.Refine.Print P4SpecTecTest.Refine.Print` passed in
1.630s (library 1.2s; test 379ms), with all exact axiom audits. Root did not rerun
that focused build; full integration gate 40282 subsequently passed.

### Actual recursive reverse certificate

Astra `/root/review_oracle_refactor` completed the recovered `exists_` induction in
`P4SpecTecTest/Refine/NanoReverseExists.lean`, with quoted-clause bridges in the
adjacent `NanoReverseExistsClauses.lean`. The public `realizes` theorem quantifies
all Boolean lists, all related raw inputs (including arbitrary notes), and every
terminating generated outcome. It constructs eventual reference execution under
guard=false, an empty local function table and the actual HoldsSpec contract.
The generated partial-correctness induction rules out error outcomes; it does
not omit them from the quantifier. It preserves the failed first alternative and
the eager recursive tail. It does not prove initialization or total termination,
and adds no generated completion binding.

Root independently read both final proof bodies, the actual generated induction
application, raw-list/Boolean relation inversion, matched-context preservation and
fuel bounds (18 for empty, recursive witness + 33). No semantic findings. The
scratch namespace was changed to the permanent test namespace on review.
Final reviewed source SHA-256: clauses
`63c7097e58b1e60b552283aaa71b0dfb1fbb845d65ecce28f0b12e53403de1eb`, induction
`265d61eedebbc8453adb18e60c765aedd3506e638aae481d1f316266fa6a9bab`.
Author `lake build --wfail P4SpecTecTest.Refine.NanoReverseExists` passed in
11.196s including clause rebuilding; all 14 exact audits use only propext,
Classical.choice and Quot.sound. The induction alone built in 449ms with warm
clauses. Independent review was read-only; full integration gate 40282 subsequently passed.
Ignored build metadata is `.artifacts/n1-reverse/exists-final-build.{log,json}`.

An implicit conversion across reassociated fuel expressions caused enormous
interpreter reduction during the initial attempt. Explicit arithmetic rewriting
and small retry/pure equalities made the final composition check promptly;
no semantic bound or recursion domain was reduced to solve this cost issue.

### Actual recursive relation feasibility

Sol's `P4SpecTecTest/Refine/NanoRelation.lean` loads 26 unchanged quoted type/relation
definitions and proves paired actual interpreter/generated execution for recursive
Type_eq and ParameterType_eq, direction mismatch, recursive type disagreement and
unequal lengths. A checked exhausted run remains distinct from a generated success.
A generic generated ParameterType_eq equation consumes the executable Type_eq
outcome directly, including failures; it requires no logical determinism theorem.
Six exact axiom audits pass. Native nested package/control/kind cases supplement
these proofs. An ignored 121-constructor-pair matrix agreed on 11 successes and
110 mismatches; it is supplementary executable evidence, not universal coverage.

Independent read-only Astra `/root/review_oracle_refactor` reviewed the final file
at `7b4e0b3`, SHA-256
`9b5b29a39060691353d99e48bba663f03cdfa3c9902de3a2a5c9ca320563dda1`.
No findings. Initialization is part of each paired kernel fact; no synthetic
callee bodies or override tables substitute for source execution. Expected-result
checks cannot accept two divergences as a matching success or failure. Positive-depth
MixopSC source checks and guarded generated projections explain why no hard error
was identified on these typed probes; universal error freedom is not proved.
The author warning-failing build passed in 7.496s; six exact audits use only
propext, Classical.choice and Quot.sound. Reviewer inspected source and build log
without rerunning Lean/upstream/full gate. Raw evidence:
`.artifacts/n1-relation/final-build.{log,json}` and `constructor-matrix.log`.
N2 retains the full recursive-group two-way certificate obligation.

### Runtime representation and configuration review

The generator now takes an explicit runtime representation profile. Nano uses
`--runtime-extern value`; unsupported profiles and extension-sensitive subchecks
fail generation. The carrier and codecs preserve raw extern payloads without
changing source quotations, packet/object membership or source constructor order.
SkipSC still succeeds; MixopSC follows the supplied source constructor test.
Same-static-type casts retain the raw value. Production-emitter fixtures elaborate
the generated declarations and check rejection of invalid configurations.

Root independently reviewed Astra's generator, fixtures and short/full packet
continuation replay, frozen staged diff SHA-256
`9ab8cec317151e104a2be727b2094f77f5bcdbf312ecc30f471767561b0ea3a0`.
Review requested an empty-profile fast path in transitive
runtime-type detection to avoid adding unnecessary full-P4 census cost; it was
implemented. The Nano library rebuilt successfully (session 63657), including
all 18 existing forward certificates. Quotations and completion metadata did not
change. The packet replay passed (author session 90544); it compares complete
canonical contexts and fresh counters, not merely output bytes.

Independent read-only Astra `/root/review_oracle_refactor` reviewed root's six-file
configuration integration against `fd7ff9f`, final diff SHA-256
`5fdc8013844988d774de00a59c3868c08737e6bd1b87d57b0db4fb315460827b`.
The review caught a coverage mutation test still using the default representation
profile. It now uses the same explicit Nano profile as production coverage checks;
follow-up review found no remaining issue. Focused warning-failing coverage builds
passed (session 11180), with all 11 invalid mutations rejected.

### Independent exit audit

The final `NanoTargetRepresentation.lean` now includes `calleeMismatchPair`: both
the actual initialized 21-definition source closure and the generated evaluator
reject the same closed runtime receiver context. Its null payload is a bounded
fixture; generic codec/source-membership facts and real packet replay cover the
separate arbitrary-payload and actual callback obligations. This is not a full
target certificate. The module has 12 exact standard-three-axiom audits.

Root independently reviewed the final module, SHA-256
`a3d0f661af43312d4a567782b0955f83d647d81ec64e9a981901b8a791635090`, including
actual source initialization, generated lookup, the generic mismatch application
and all representation/copy-out assumptions. No findings. The author's focused
warning-failing build passed (session 75128, module 22s).

The initial normalization attempt hit a lazy imported-equation budget, not a
semantic counterexample: reducing the lookup tried to generate all 48 builtin
dispatcher equations under import-time options. A local `cbv_eval` rule proved
by `rfl` for the actual `find_maps` branch bypasses that work. No dispatcher,
interpreter semantics or package-wide budget changed. Astra
`/root/review_oracle_refactor` contributed this diagnosis and independently ran
the minimal source proof (21.333s, standard axiom audit); root supplied the
independent integrated-proof review.

Sol `/root/organize_lean_tests` independently compared the implementation with
the N1 exit at `591eb60bfbb74b006dafcaee095f24dfa2601ae8`. The only remaining
implementation item was the paired actual source/generated raw-receiver kernel
fact; final review and integration gates were also pending. No additional N1
scope gap was found. The runtime design/decision diff SHA-256 was
`2ac9d3f46f4a0aa56211624209e3a35a58cab2f3e83a38ff00a5e91ddb29d26d`;
review was read-only, without builds.

The audit preserves two distinctions: actual subsequent AL receiver selection
returns `unmatch`, whereas direct raw-receiver target dispatch returns `err` on a
separate path; typed relation probes establish no universal error-freedom result.
Full recursive-group certificates and domain adequacy remain N2, while complete
target/boot/STF composition remains N4.

Sol separately reviewed the public capability text, retained target note, CLI
documentation and new test-root import at `591eb60`, diff SHA-256
`a1496aa952e825a3c2a86b223332f12da3863153e4564200939d1dc8ce7aacf4`.
The one wording finding was resolved by describing the full-context comparison as
canonical equality and the fresh-counter comparison as exact. Context equality
compares externs by compressed JSON; it does not compare source notes/regions.
No other finding; this review did not run builds.

## Plan review and validation

### N1 integration checkpoint

The full local gate `nix develop -c bash
/Users/qobilidop/my/work/p4-spectec-lean/scripts/check.sh` passed with actual exit 0
(session 40282, 104.859s), all 44 stages and no skips. Ignored raw evidence is
`.artifacts/n1-full-gate.{log,json}`. This includes both 78-program typing replay
legs, packet/verify replay, existing certificates and mutations, generated freshness,
coverage/quotation checks and the full-P4 census. Source pins, quotes, completion
counts and corpus denominators are unchanged. Final prose receives text/link checks.

All three N1 implementation exits now have checked evidence:

| Workstream | Selected interface and evidence | Retained boundary |
|---|---|---|
| Reverse execution | EventuallyRuns/Realizes composition, actual exists_ induction, actual recursive relation probes | N2 owns universal generated two-way/domain/initialization contracts |
| Target representation | Explicit raw runtime carrier, generic codecs/source separation, paired receiver failure and actual extract context replay | N4 owns complete target/boot/STF composition |
| Printing | Canonical relation plus explicit empty hints, actual builtin/global dispatch preserving results and errors | Hinted specifications require stronger provenance; N2 owns broader primitive contracts |

The selected interfaces have no unresolved N1 counterexample. This establishes
feasibility, not full Nano certification or new generated completion bindings.
Publication and exact-final-revision remote CI remain pending at this checkpoint.

Independent read-only Sol checkpoint review at `591eb60`, four-file documentation
diff SHA-256 `7038caa80711d66eb860a8863b38af10f6b870c4dd79c476d12f3d21696a44be`,
confirmed the bounded N1 claims and retained N2/N4 obligations, and independently
read the gate's successful result. Three stale focused-build paragraphs saying
integration remained pending were corrected to point to gate 40282. Text hygiene,
whitespace and all 69 relative file-link targets passed after the checkpoint rewrite.

### Historical plan validation

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
checks afterward. No new implementation or theorem is claimed by this historical
plan checkpoint; later implementation validation is recorded above.
