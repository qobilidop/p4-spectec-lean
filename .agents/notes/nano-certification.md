# Nano-P4 certification implementation plan

Remaining plan and durable evidence, updated 2026-09-29. N0/N1/N2 are closed (N2
closure `d85e82c`). N3-owned proof closure is complete at `67f67ae`, with passing
local/remote gates and independent review; broader core acceptance still needs
N4-owned corpus evidence. The earlier stabilization checkpoint `770e405`
passed the full local gate and CI. N4–N6 remain planned, and full-P4 M3 remains
paused.
[Design section 9](../../docs/design.md#9-nano-p4-scope-and-acceptance) owns scope,
[Certification](../../docs/certification.md) owns delivered artifact guarantees,
and [status](../status.md) owns the next immediate action.

## Scope and baseline

The unchanged pins cover 350 source declarations: 162 types, eight schematic
variables, 76 functions, 77 relations, 26 builtins and one extern relation.
N0 established the complete obligation inventory and pinned corpus accounting.
N1 closed at `56cf92c` with
[CI 36290916636](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36290916636):
reverse execution, recursive relation feasibility, unhinted printing and faithful
runtime raw-extern representation on actual callback paths. N2 supplies the
reusable source-domain and call contracts below. Full core and target
composition remain separate acceptance stages.

## N2 evidence (closed; constraints still bind)

- All 162 declarations have generated full-source codecs: encoding validity,
  decoder soundness at arbitrary fuel, and stable sufficient decoding for each
  source value. Recursive/nested families use source derivations and actual
  carrier induction; parameter codecs and dictionaries remain explicit.
- At N2 closure both correspondence directions covered 39 of 153 bodied declarations
  (68 at the historical first N3 checkpoint, 153 at stabilization). The strict
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

## N3 proof closure (complete)

The first checkpoint on `main` reached 68 of 153 bodied definitions; its
blockers and review are historical. At stabilization checkpoint `770e405`, all
153 bodied definitions have compiled forward and reverse theorems, including
`Decl_load`, `bin_op`, `Expr_eval` and the six-member `Call_eval` group.
Relation run-soundness covers all 77 relations. The full local gate and CI
passed. Extern-dependent theorems assume the abstract `externsContract`;
print-dependent theorems assume `cfg.printHints = []`.

The evaluation domain uses the runtime-inclusive profile where the source-only
profile is incomplete. The final four domain contracts (`ite`, `repeat_`,
`empty_set`, `empty_map`) now compile under arbitrary legal parameter codecs.
The completion CLI checks source identity separately. The inventory has 888
obligations and 762 compiled claim bindings. The normal gate now requires
`--require-owned N3` as well as bounded N2; later-owned core corpus, target and
release obligations remain open. See [the source-domain checkpoint](n3-source-domains.md)
for proof/review evidence and [status](../status.md) for validation and integration.

Reusable support now covers relation output premises, recursive subtype bridges,
numeric coercions, guarded cast unfolding, relation pattern iteration, membership
conflicts, generated traversals, no-output calls and sliced inputs. The
`scripts/replay-cert.py` tool speeds tactic iteration but is not certification
evidence. Earlier WIP blockers and their reviews remain recoverable in Git history
at `b6f1576`.

## N2 closure verification (historical)

The corrected full local `nix develop -c scripts/check.sh` returned actual exit 0
(session 47761), all 44 stages with no skips. It includes exact compiled theorem
types/axioms, strict N2, quotation/generation freshness, both replay legs and
field-update mutations. Source checks cover 342 ordinary declarations and eight
typed variables; compiled coverage checked 806 claims. The manifest then had
888 obligations, 381 bindings and 507 unresolved, independently of the strict
30-definition N2 closure.

Implementation `76bed8485032a6bb2e95b248b37f99dcf0c45267` passed
[CI 36314414521](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36314414521).
Closure-only `d85e82c02a4d714bdcc7a78ee681cf64490aee78` passed
[CI 36316496027](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36316496027).
Both include the full gate and pin checks. The merged N2 branch is removed.
Earlier CI at `9668c63` failed only because inventory tests read the ignored raw
export before unpacking; the fixture now reads the committed gzip directly.
All 36 tests passed with raw input temporarily absent (18940). Warm artifacts
must not be the only evidence for a fixture's input availability.

Independent AI-agent reviews used Astra (`organize_oracles`,
`review_oracle_refactor`), Sol (`organize_lean_tests`) and root cross-review.
Each excluded its own authored changes. Reviews were scoped to the recorded
diffs; they are separate from kernel checking, full gates and upstream evidence,
and are not human review or a fresh proof of the reference interpreter.
No unresolved findings remain. Resolved findings included parameter
shadowing (explicit scoped dictionaries), mutual output-column eligibility
(single-self-SCC restriction), and empty-substitution traversal (fast path).
Actual production codecs replaced the obsolete handwritten TypeIR encoding
probe only after five replacement witnesses passed with axiom audits; unique
negative and mutation tests were retained.

The 54 original review records, exact file hashes, findings, resolutions and
limits are recoverable at the historical Git path
`d85e82c:.agents/notes/nano-certification-review.json`. The chronological gate
history is in that revision's Nano note. Ignored logs are supplementary scratch,
not required resume or release evidence. Reusable constraints remain above and
in Decisions; strict N2 does not close broader core, target or release stages.

Observed proof cost: the first expanded remote library/certificate build took
1534s, including 938s for Type_eq; a local Type_eq build took 235s. These are
uncontrolled observations, not comparable benchmarks or additive wall times.
Profile the remaining proof costs before expanding expensive recursive groups.

## Standing constraints (from N2, still binding)

Prove invariants at initialization and preserve them at every call; do not add
hypotheses that no actual caller can establish. Extend both proof directions
together; implement ordered relation attempts, negative premises and recursive
groups without requiring every logical relation to have an exact converse; preserve
the run-soundness layer, and prove determinism only where a proof or client needs it. Reachable legacy
matching/substitution fallbacks must be replaced or proved unreachable on the
admitted domains before certifying them. Reusable support stays outside
`ExampleProofs`; generated files are never patched by hand. The N2 plan text is
recoverable at `d85e82c:.agents/notes/nano-certification.md`. Primary surfaces:
`Codegen/Types.lean`, `Codegen/Funcs.lean`, `Codegen/Certificates/Forward.lean`,
`Codegen/Emit.lean`, `Refine/`, `Tactic/` and `P4SpecTecTest/`.

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
The core check for obligations owned through N3 (`--require-owned N3`) passes,
with target-dependent results explicitly conditional on the named extern contracts.
The broader core stage still requires N4-owned corpus evidence. No missing callee or SCC member
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

## Execution constraints

Preserve all 78 typing programs and 39 STF sessions. Only three STF sessions have
stored observations; missing observations are not successful replay.
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

## Historical effort estimate

Planning forecast discussed with the user on 2026-09-27; moderate-to-low
confidence, superseded by the 153-definition stabilization checkpoint. The
four final N3 domain contracts now compile; no current effort estimate
is recorded here. The earlier forecast used elapsed working hours
with the current lead and targeted specialists, including review, integration,
builds and validation, not summed subagent-hours or a calendar commitment.

| Milestone | Working estimate | Main uncertainty |
|---|---:|---|
| N3: complete core semantics | 16–32 hours; revised 30–45 | Remaining iteration/polymorphism, recursive groups and call/context invariants |
| N4: target composition | 12–24 hours | Typed callbacks, intermediate state, initialization and full packet observations |
| N5: whole-program theorem | 4–8 hours | Usability of completed N3/N4 contracts |
| N6: release evidence | 4–8 hours | Scope audit, mutations, performance and final validation |

The forecast's base total was 36–72 hours, with 45–90 including contingency.
Definition and obligation counts are not effort percentages. N4's typed target
and packet observations remain a major semantic uncertainty.
