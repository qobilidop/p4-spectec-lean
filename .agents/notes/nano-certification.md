# Nano-P4 certification implementation plan

Active plan and durable checkpoint evidence, updated 2026-09-27.
N0/N1 are closed. N2 implementation, strict compiled checking and the full local
gate pass; publication and exact-revision remote CI remain pending. N3–N6 remain planned.
The user authorized completion through N2; full-P4 M3 remains paused.
[Design section 9](../../docs/design.md#9-nano-p4-scope-and-acceptance) owns scope,
[Certification](../../docs/certification.md) owns delivered artifact guarantees,
and [status](../status.md) owns the next immediate action.

## Scope and baseline

The unchanged pins cover 350 source declarations: 162 types, eight schematic
variables, 76 functions, 77 relations, 26 builtins and one extern relation.
N1 closed at `56cf92c2201e25c11d1263cbdf6895a827afc612`, with all 44 local gate
stages passing and [CI 36290916636](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36290916636).
N0 established the complete obligation inventory and pinned corpus accounting.
N1 established reverse execution, recursive relation feasibility, unhinted
printing and faithful runtime raw-extern representation on actual callback paths.
Those probes did not complete full core or target composition.

The pre-continuation N2 checkpoint `c8f78f7` passed the full local gate and
[CI 36294851006](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36294851006).
It covered both directions for the original 18 functions and dispatch contracts
for all 26 builtins; source-domain and call invariants remained open then.
Local continuation commits `feec9b6`, `996dc22`, `9863160` and `709326f` establish
syntax-derived substitution bounds, independent source grammar, codec composition
and explicit nominal decoder dictionaries. The final continuation adds the
production bindings described below.

## Current N2 evidence

- All 162 declarations have generated full-source codecs: encoding validity,
  decoder soundness at arbitrary fuel, and stable sufficient decoding for each
  source value. Recursive/nested families use source derivations and actual
  carrier induction; parameter codecs and dictionaries remain explicit.
- Both correspondence directions cover 39 of 153 bodied declarations. The strict
  N2 exit requires the original 18 plus Type_eq/ParameterType_eq, Type_ok and
  Var_init, with their complete 30-definition dependency/SCC closure. It also
  requires source input coverage, successful source outputs and every actual
  intermediate call domain. Additional emitted claims do not shrink that scope.
- All 26 builtins have exact dispatch and both invocation directions, plus full
  source input coverage and universal admitted-input output preservation under
  explicit legal parameter codecs. Defined in_set/dom_map/codom_map have separate
  source-domain contracts; ValueBEq remains an execution-contract requirement.
- Primitive/container codecs, eight source-order typed VarD omissions and actual
  table initialization have separately checked schema-3 profile claims. VarD
  are schematic declarations, not invented initialized runtime values.
- Call arguments with wholly admitted carriers have universal codec-based
  admission. Three restricted runtime-value cases need stronger source proofs:
  updater suffixes; context maps/keys/payloads/intermediate key sets; and Var_init
  call prefixes. The last requires only successful *earlier* calls, including
  default, without assuming the current or final call succeeds.
- Actual tuple results use exact two-field dictionaries; the right component is
  one value even when a generic parameter is a product. Closed right products
  whose ambient encoding would flatten are rejected. Unit covers zero-output
  relations. No generic ambient product decoder is assumed.
- Source substitution has a proved syntax bound. Type_eq/default use MixopSC;
  Type_ok's RecurseSC sites are numeric Nat checks. The selected source paths
  do not call the legacy total matcher/substitution fallbacks. Indexing/slicing
  and other absent constructs remain explicit later-inventory obligations.

The source domain follows the pinned constructor grammar, not broad runtime
Match.sub acceptance. Make.nat/int preserve tags; elaboration inserts UpCastE and
OptE; interpreter casts change numeric tags and optional iteration makes OptV.
Cross-tag numeric membership and bare optional membership remain explicit
counterexamples to identifying runtime subtype checks with this grammar.
Call/producer certificates establish composition rather than assuming that
membership supplies source validity. The declared objectState extern domain
admits arbitrary JSON; the additional value.runtimeExtern carrier constructor
is excluded from the source value grammar. General target composition remains N4.

## Verification and independent review

Production aggregate 40739 passed 580 jobs. After the final call-domain and tuple
integration, `nix develop -c lake build --wfail NanoP4Spec.Refinement` passed
16874 (621 jobs); Type_eq took 235s, context insertion 3.1s and Var_init producer
589ms. These are warm/incremental observations, not controlled performance
comparisons. Exact coverage/quotation plus `--require-n2` passed in the first full
gate (46818, 38s). It checked 806 compiled claims, 342 ordinary quoted declarations,
eight typed variables and the actual source profile. The manifest retains 888
obligations, 381 bindings and 507 unresolved; broad core completion still fails.

The first complete gate returned exit 1: old Unit/tuple-negative fixtures,
a reserved test binder, an obsolete handwritten TypeIR encoding probe, one text
line and a mutation extraction boundary. The new semantic production proofs and
strict N2 check passed. Fixes preserve negative arity/mode checks and the actual
mutation runner passed (18s). The retired 631-line probe contained no unique
mutation tests; five actual codec.encodingValid(admittedAll) replacement witnesses
passed with audits (80617). A second complete gate found only two unused simp facts in the downstream example;
removing them preserved the exact theorem and axiom audit, and ExampleProofs then
passed 60286. Final full gate 40389 passed with actual exit 0, all 44 stages and
no skips, on index tree `e654712bd9385535ec73c3a88b883b57054036fe`.
Logs and stage results: `.artifacts/n2-closure-gate.{log,json}`. Subsequent
checkpoint prose leaves executable inputs unchanged; exact-revision remote CI
remains the publication obligation.

Independent read-only reviews are preserved in
[nano-certification-review.json](nano-certification-review.json), including exact
file hashes, reviewer provenance, original findings, later resolutions and limits.
Astra reviewed difficult semantics, recursive codecs and root integration; Sol
reviewed the completed builtin/prefix contracts and strict validator; root reviewed
agent-authored renderers, tuple proofs and final fixture changes. No AI review is
represented as human review. Generic proof tests, actual generated certificates,
negative eligibility mutations and exact compiled-type/axiom checks serve distinct
obligations. The 36 Python inventory tests pass; no JSON boolean certifies a
proof. Artifact log paths are local scratch, not persistent release evidence.

The gate now invokes `scripts/nano-certification.py --require-n2` after building
and freshness checks. It requires every source type identity, all eight variables,
all 26 builtin dispatch/invocation/domain contracts, primitive/initialization
profiles and the full selected closure. Partial context projections cannot replace
complete call contracts. Broad `--require-complete core|target|all` remains
independent and incomplete. Final full-gate exit and exact-revision remote CI must
be recorded before N2 is marked closed.

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

## Execution after N2

N3 is the next proposed increment; do not automatically start broader work during
N2 publication. Preserve all 78 typing programs and 39 STF sessions. Only three STF
sessions have stored observations; missing observations are not successful replay.
Full-P4 M3 stays paused. The dynamic NanoSwitch port and shared verify ABI limits
remain in [nano-target.md](nano-target.md). Source identity, core semantic
initialization, target composition, packet observations, whole-program proofs and
release evidence cannot be inferred from the N2 representation/contract milestone.

Use the existing generator, libraries and colocated tests. Avoid a new parallel
semantics or name whitelist for ordinary proof selection. The strict N2 root list
records agreed milestone scope; proof eligibility still follows source structure.
Retain actual counterexamples and trustworthy failure classifications. Git history
holds superseded experiments and chronological probes; this note holds current
claims, constraints and the remaining plan.
