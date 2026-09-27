# Nano-P4 certification implementation plan

Active Nano completion plan and retained milestone evidence, 2026-09-26.
N0 and N1 are closed; N2 is active and N3–N6 remain planned. The user approved autonomous execution
after the planning checkpoint, starting with N0/N1. The contract is
[Design section 9](../../docs/design.md#9-nano-p4-scope-and-acceptance), not this
work breakdown. Both core semantics and target composition must close.
Broader full-P4 M3 remains paused. The user explicitly resumed implementation
after organization/performance work and authorized completion of N1. Its proof,
representation and observation exits are now closed. Broad proof generation is
now authorized through N2. The active implementation checkpoint follows below.

## Baseline and critical path

Scope revision: `da631a9988298bb8705f2e9d0df3306092454f40`. Baseline coverage
contains 76 functions, 77 relations, 26 builtins and one extern relation.
There are 18 forward AL certificates, 77 relation run-soundness theorems and
two logical determinism theorems. Generated reverse coverage was absent at that baseline;
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

### Active N2 implementation

The user authorized N2 after closure revision `56cf92c`, whose exact final
[CI 36290916636](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36290916636)
passed. Work is split by owned files: Astra develops independent source-domain,
representation and sufficient-decoder interfaces, and generic generated reverse
proofs; Sol develops operation-specific builtin contracts; root integrates
initialization certificates, coverage validation and generated outputs.
All 26 builtin declarations and the full N2 exit remain in scope. Initial
interfaces do not by themselves discharge source-domain or call-preservation
obligations, and no new manifest binding is claimed without its checked adapter.

#### Continuation: syntax bounds and source inventories (2026-09-26)

Active local continuation on `n2-certification` of published `c8f78f7`; its remote
CI run 36294851006 passed before this work. The substitution checkpoint is local
commit `feec9b6`. No full gate or publication is claimed for this evolving tree.

Root implemented `Runtime/Type/SubstDepth.lean`: input-syntax depth bounds for
checked type/list/notation substitution, definitive-result proofs and stable
results for every larger type/list budget. All production checked substitution
calls now use these bounds; alias expansion and membership retain their separate
execution fuel. Errors, simultaneous replacement and the empty-substitution fast
path are preserved. Legacy total APIs remain separate. Focused validation:
`lake build --wfail P4SpecTecTest.Runtime.Type.SubstDepth
P4SpecTecTest.Runtime.Type P4SpecTec.Refine.Environment`, session 66512 exit 0.
The executable regression distinguishes the former cutoff at depth 1,100 and
checks replacement non-recursion and retained higher-order/function errors.
Artifacts: `.artifacts/n2-substitution-depth-test.log`.

Independent read-only Astra review at base `c8f78f7` found no semantic issue and
one low performance issue: computing the syntax bound eagerly for an empty
substitution. Root moved the empty check before traversal. Reviewer confirmed
resolution at SubstDepth SHA-256
`b9d0024fdb8c8afa564239276243e4ad2330ea17e8df58e4de49dbd98dfd6be4`.
The original six-file hash inventory, finding and later resolution remain in
`.artifacts/n2-reverse/substitution-review.json`. Limits: no independent build or
performance measurement; alias expansion/membership bounds are not discharged
by this substitution theorem.

Root's separate equality sidecar supplies all 161 actual generated `ValueBEq`
instances without parameter equality or injectivity assumptions. The production
sidecar and a noninjective erased-parameter regression passed `--wfail`.
`Init.globalTypeAbsent` proves source-undeclared names remain absent after full
table initialization. Generated freshness facts passed for the actual Nano
quotation (`.artifacts/NanoInitFresh.lean`, session 21517 exit 0); a fixture checks
that a same-named global type is excluded from these facts. Independent read-only
Sol review found no issue across the six-file equality/freshness snapshot
SHA-256 `ea7395e3fd68ae9621962d34350f7425d8b4e240670979b51a2327c1ed095649`.
Limits: inspection plus author's focused results, no independent full gate.
Later representation-inventory edits in Emit require a separate integration review.

Source codecs are being integrated into a separate type inventory in coverage
schema 2. The completion denominator is unchanged; caller domains, initialization
and primitive/container obligations stay independently tracked. Nineteen Python
adapter tests pass, including rejection of missing, duplicate, misclassified and
wrong-source type entries. The integrated generated certificate and compiled
coverage test subsequently passed with `--wfail` (session 89912, exit 0, 201 jobs),
including the original 18 two-way functions, new in_set two-way certificate,
seven atomic source codecs and fifteen exact-boundary mutations. Evidence:
`.artifacts/n2-source-coverage-check.log`. Regeneration used relative
`exports/nano-p4.al.json` with `--runtime-extern value` (session 74812 exit 0);
completion metadata update (49976) and nineteen adapter tests (49449) passed.
The local inventory has 148 checked bindings and 740 unresolved obligations,
with 888 total. This is a focused integration verdict, not a full gate or N2 closure.

#### Independent source-domain support checkpoint

The finite `Representation.Source.Valid` grammar reads actual type declarations,
uses strict source tags and positional constructor fields, and keeps external
source domains explicit. Relational substitution is unbounded and simultaneous,
with the source's last-binding-wins convention. Type-namespace lookup excludes
same-named variables/functions. `SourceSubst`, `SourceAlias` and `SourceContainer`
prove substitution inversion, metadata transport, and actual set/pair/map source
construction and inversion. `SourceMixfix` preserves arity and canonical fields
and transports notation matches across carrier types. `DecoderCorrect.delay`
composes captured alias decoders with a one-step bound increase.

Actual generated ByteText aliases capture distinct dictionaries: id consumes one
layer, callableId two, nameIR three and typeId four. A checked explicit typeId
soundness/sufficiency proof uses its named decoder and the primitive dictionary;
ordinary type-class inference must not silently replace that decoder. This is
support for actual SCC codecs, not a completed recursive-decoder binding.

Focused validation passed with `--wfail` for
`P4SpecTecTest.Refine.Representation.Source`,
`P4SpecTec.Refine.Representation.SourceContainer` and
`P4SpecTec.Refine.Representation.Delay` (49 jobs, exit 0). Exact theorem axiom
checks passed. The source test keeps distinguishing namespace/substitution/tag
checks; the handwritten direction-codec feasibility proof was removed because
production codec emission and its tests now cover that obligation.

Independent reviews, based on `feec9b6` with the specified working snapshots:

- Sol `/root/organize_lean_tests` reviewed source grammar and its reduced test,
  snapshot `32325955d3ea241dcb00c612043596ae2069fe39b71ed71bea7a215da0a8db79`:
  no findings. This is not a characterization of all runtime Match membership.
- Astra `/root/review_oracle_refactor` reviewed container construction and delay,
  with no findings; later inversion additions received a separate read-only
  review from `/root/organize_oracles`, also no findings. The latter also reviewed
  SourceAlias's original declaration/alias inversion. Astra separately reviewed
  all later alias/substitution/container metadata-transport and inversion additions
  at the final hashes below, with no findings. Root independently reviewed the
  notation fork/transitivity laws and their exact source-only assumptions.
- Final source snapshot hashes: Source
  `9e8ed5d313493721fc422fa02a0d6e74ef6771b3c35f2efc000ccbb91068a291`, SourceAlias
  `96c4c7ee1cb76641f66d0da34268d0f0882f1c2dfead4a6c688564664e54bce2`, SourceContainer
  `8fc6189c825ca5a5e031b37de02473a27a4586e0f9e5738a8692e2f6d0af3bd2`, SourceMixfix
  `2931f8cc3d529b12e082255c27e48587cc8946bbf646064288113bf2d2f29fb3`, SourceSubst
  `e53d73aa4ab11cfcb677cef0e33309e6d2c4d7287b866ff171e77a3a272e8d2f`, Delay
  `e99782b9e1500108f5d71cee12dff84bd92c39e91b98859975cece6be559ae03`.

Review limits: inspection and author validation; no independent full gate or
claim that all Nano source families now have codecs. Recursive encoding evidence
for TypeIR against the complete actual quotation passes separately (74 jobs,
TypeIR module 3.9s); source-derivation decoder proofs are still active.

Separate schema-2 integration review by Sol found no issue in the seven-file
snapshot `74cb643cde954b776c88eae6dba2a1fe77cda1de41862e59a78a79aef23a76f8`.
Both type and callable claims retain exact compiled theorem/axiom validation;
source codecs bind only representation obligations. Source-domain, initialization
and primitive obligations remain separate. No full build was repeated by reviewer.

#### Continued source and caller integration

Local source support now includes `SourceCodec` primitive/list/option contracts,
`SourceVariant` constructor-domain inversion/construction, `SourceAtomic`'s
agreement between the two independent atomic grammar interfaces, and nominal
identifier metadata transport. Exact axiom checks and focused `--wfail` builds
passed (sessions 48896 and 69748; final 33 jobs). These preserve strict numeric
tags, positional fields, actual declaration membership and substitution premises.

Independent read-only Astra review by `/root/review_oracle_refactor` found no
issue in SourceCodec SHA-256
`dfd5c85a07c6243d7f9fa24ec56ba12838eef07c436d0bc9b63f2d3ef299571e` and SourceVariant
`9cfa941a00266650626efc355a135dc20571c8bfd6b3dfeb219ba3081db42692`.
Evidence: `.artifacts/n2-reverse/source-codec-variant-review.json`.
Astra `/root/organize_oracles` separately inspected SourceAtomic and nominal
metadata transport, with no findings. Limits: read-only inspection, no independent
build and no whole-Nano representation claim.

Text-alias codec generation binds both named encoder and named decoder explicitly.
The synthetic alias-chain test distinguishes captured fuel layers and rejects
cycles, unknown declarations and runtime-extended aliases. Independent read-only
Sol review found no issue in the three-file emitter/test snapshot SHA-256
`b2646d420fe817d04c8254e26e1bdb782fcb5d1b8fa5df3f489ff9e9620a4035`.
Focused emitter/test checks passed; the four actual generated alias sidecars and
the generated dom_map/codom_map two-way sidecars passed together with `--wfail`
(session 97707, 117 jobs). Relative-input regeneration wrote 91 files (35911,
exit 0). The exact aggregate coverage checker has not yet validated this expansion.

Actual dom_map plus add_var_e forward/reverse composition passed all four audits
in 41.045s, using production in_set/add_map contracts and transitive K/V freshness.
The full Type_ok forward closure passed in 71.693s, and typeIR_of_typeDefIR reverse
passed in 37.600s. These are focused probes; conservative production caller
eligibility and the remaining reverse closure are still being integrated.

The complete TypeIR SCC has source encoding-validity and unconditional stable
source-decoder sufficiency against the full actual quotation, at arbitrary depth
(combined probe 29078, exit 0, no Lean warnings). All eleven actual TypeIR decoder
constructor soundness lemmas also pass, with exact axiom audits (44406, exit 0).
The full recursive soundness assembly and generated production bindings remain
open. At least 92 source families occur in the original eighteen input-type
closures; this is a lower bound that excludes separately collected result types.
Generic emission must cover those dependencies, including recursive and legally
instantiated containers, rather than treating the TypeIR probe as N2 completion.
No full gate or publication is claimed on this evolving continuation.

#### Explicit nominal decoders and continued composition (2026-09-27)

Closed nominal fields now call the decoder named by their source declaration,
passing explicit child dictionaries. Primitive and list/option fields recursively
bind those dictionaries too. Local type parameters shadow global declarations in
carrier, encoder and decoder generation. This prevents an unrelated reducible
alias or a hostile ambient primitive instance from changing field decoding.
Source aliases retain their own decoder frame; old incidental fuel thresholds
are not a compatibility promise. Nonrecursive tuple and function dictionary
selection remains outside this change; the actual Nano field census has neither.

Astra `/root/organize_oracles` independently reviewed the Types emitter and
fixtures at base `9863160`. The original finding was global `K` capturing a
bound `K`; scoped lookup/member filtering and a global-Boolean-versus-bound-text
fixture resolve it. Final review found no issue. Reviewed Types SHA-256:
`db7bb27e1b7972ee174d764b5658d2ca8e781bc54d1b87f459dcb302580b3fdf`;
fixture `698fea34b66dccff4f8dbfaecb7cd085393b021e33bb621d928dd518fb922acc`.
Focused warning-as-error checks passed (61214, 42 jobs). Generator build 87191
and regeneration 97363 passed. All regenerated carrier modules built in aggregate
33016, but that aggregate failed on fifteen newly enabled function certificates;
this is not a passing full gate. Later structural frontier restrictions exclude
fourteen unsupported combinations, while the remaining `add_callableDef_l`
proof passes after generic optional-record-field normalization. Independent
Astra review of the caller snapshot `6575ac2578523581dcb0fb2310473961fde971d63e87939a8f87b175a716b37b`
found no issue; regeneration/aggregate validation remains pending.

The actual Type_ok closure passes both directions in a composed emitted probe
(132.378s, source SHA `7c3aa4505d77bb12b0161dd456af19031ceb7cc956eb942ab1f42defe131b6ce`).
Five recursive source codecs using the new named decoders pass with 103 axiom
audits and no Lean warnings (46674); source artifact SHA
`afa8a56f41d6804532162fd72ac5468e5ee74f18bdf4da7ad7c3416ae912a9ec`.
These remain staging evidence until generic production emission is checked.
Actual Type_eq/ParameterType_eq reverse and forward probes pass separately
(157.81s and 118.57s); a final combined source-derived production-renderer probe
and review are pending. Full arbitrary related inputs and failure outcomes are
retained. No determinism assumption or fixed source depth was introduced.

Root independently reviewed source records, field contracts/domain transport,
shared traversal observations and the exact output-free interpreter iteration
lemma; no findings. Ignored exact hash/evidence records are
`.artifacts/n2-record-review.json` and `.artifacts/n2-shared-proof-review.json`.
Generic polymorphic pair/list-container/map-alias codec fixtures now pass for
renamed source declarations and arbitrary legal parameter codecs (44 jobs,
40663/73169). The codecs, shared field resolver and broader variant/record
emission are still being integrated. Recursive SCC emission, at least 92 input
source families, actual call preservation and Default/Var_init remain required.
No new full gate or publication has occurred.

#### N2 checkpoint review and validation

- Generated `Refinement/Environment` now owns actual checked `Ctx.init`,
  `HoldsSpec` and empty local-function environment proofs. The field-update
  consumer imports these rather than owning a duplicate. This proves table
  initialization only, not semantic program initialization or source domains.
  Sol independently reviewed the ten-path snapshot at baseline `56cf92c`,
  SHA-256 `9b4aa652334ae30a07f2ccce3c81d302fad0af06ab6268dc23a463159d9cde64`:
  no findings; proof statements and consumer requirements preserved.
  Focused `--wfail` build session 23150 passed (environment 20s, emitter
  fixture 354ms, correspondence 7s, certificate 354ms).
- The generic builtin invocation bridge preserves actual dispatch outcomes
  with three entry steps and explicit guard/lookup assumptions. Sol's read-only
  review of Invoke/Print at `56cf92c`, snapshot SHA-256
  `8ca96fcbdcb2d5ffaae95457fbb11f5eaf2d6dcccbf2284f5d60301dbfab5469`, found no
  issue; existing Print theorem types and failure distinctions are unchanged.
  Focused `--wfail` Invoke/Print/tests passed session 12367. Later canonical-run
  composition additions require another review and are outside that verdict.
- Root independently reviewed Astra's frozen `Representation.lean` and its
  tests (SHA-256 `292a497144d20aa1305871e327fec8aaad5528495df46f7921e6e10d82593b23`
  and `c4d4e69e780e56b35624194bb7a17023abb74d76cb047efdc4b5169e27b4ef66`): no
  semantic finding. Source predicates remain independent; admitted carriers,
  decoder soundness and stable sufficient fuel are separate obligations.
  Recursive tests start from an independent source grammar. The three checked
  numeric/optional membership counterexamples prevent claiming runtime
  membership alone is a representation domain. Focused `--wfail` session 62076
  passed (444ms library, 404ms tests). Actual Nano grammar/call-invariant bindings
  remain open; these abstract contracts do not discharge them automatically.
- All eleven numeric operation contracts and their single combined universal
  actual-Nano-wrapper test pass `--wfail` (session 27435, 1.4s library, 351ms
  test), including width-boundary and empty-bit-array failures. Sol independently
  reviewed snapshot `c16dd7eb659aa467702e9c0c7e56da5e9f33600e3242499f46ee9b8768aea9de`
  with no findings in that represented-input scope. The later all-eleven value-arity
  theorem also passed review (library SHA-256
  `14766f342343b095e3ac78fab22991053219b84cbae1faf3054b3cc0c1ed941a`), retaining
  ignored type arguments. Final focused session 18586 passed (1.6s/424ms).
  Sol reviewed canonical-run adapters and the actual quoted-builtin reverse
  application (snapshot `f69f4216c81b1ee0bcc27bb3dafdc113b7fac8ac2ba0cf182d710ef147c41d61`)
  with no findings; focused sessions 81487/4554 passed. These are operation and
  invocation contracts, not source-domain establishment.
- Root independently reviewed Astra's ordering/normalization library and tests:
  snapshots `ec897a63ba30448d1423457587f5029b066e209e495f12fbf8b822742b2d8829`
  and `735242110d931aff87bbdc55cd330a8e553e11b049cb37a22effe9b2fc29cd73`.
  No semantic finding: structural comparison yields a total preorder on
  observations, not equality of arbitrary carrier fields; normalization
  idempotence preserves exact chosen representatives without encoder injectivity.
  Generic proofs preserve original extern JSON compression. A separate executable
  regression shows that comparing canonical externs again can reverse ordering;
  it is not advertised as a kernel theorem. Focused `--wfail` library/tests
  passed with actual exit 0 (26s/365ms).
- Sol reviewed the final all-fuel invocation adapter (Invoke SHA-256
  `fd0b55ac30eb0cb58b627894bf5006e68e0ed619d0c98c511e03f0acb7a199f9`)
  with no findings: fuel 0–2 exhaust, and all larger fuels use actual dispatch.
  Focused `--wfail` session 1691 passed.
- Root independently reviewed Sol's Text/List/Collection/Map libraries and tests
  at their frozen revisions, with no findings. All eight operations preserve
  canonical results and actual failure distinctions. Ordered maps retain
  first-match lookup and replacement, with no uniqueness assumption. The final
  seven-file focused build passed with actual exit 0 (0.584s warm);
  `.artifacts/n2-builtins/final-focused.{json,log}` retains local evidence.
  Library hashes: Text `d9867146411d27ee61547df19d16c6ffea03b3bf1e7b0049d1d1cc0ca40c36e3`,
  List `b6a6403d6db3690d3555569131652652711926be19cc59851fcac4af436d44c3`,
  Collection `a9b69814e018ef5eb324821e0f3e322b8fb9081e80f12ea0c83f889ecd1f8a6f`,
  Map `e7b8fbe0e178f086b556654b94c1b84395aef27d4e893af30428319949771f18`.
  Tests bind actual Nano wrappers; production generated builtin certificates
  are a subsequent integration step, not claimed by these reusable contracts.
- Root independently reviewed Astra's final set library and tests, SHA-256
  `b13128cddfaf215b4da109270d4c9293e5e523415efe9dabdbd81ea91e34a2a1`
  and `c45fc267c40adb649be6a93373a9e2b3c9b8504a6a69abb08ea004e3b6f734dd`:
  no findings. Six actual dispatcher contracts preserve canonical ordering,
  normalize twice safely, retain non-injective encoder representatives, and
  cover malformed shapes and arities. Focused `--wfail` session 83739 passed
  (1.4s library, 372ms tests). This completes reusable operation contracts for
  all 26 builtin names, not independent source-domain establishment.
- Sol independently reviewed direction-specific coverage/frontier handling and
  the reverse manifest adapter at baseline `56cf92c`, five-file snapshot
  `a66afa4352a340d39d2919ce1355cf4f912129162b957bf61bf0e74c3a5555cb`:
  no semantic findings. A stale forward-only adapter docstring was corrected
  after review. Focused coverage session 20406 and all 16 Python adapter tests
  passed. Reverse dependencies remain separate from forward dependencies;
  represented-input evidence does not close source-domain obligations.
- The handwritten N1 recursive exists_ regression remains: its intermediate
  result fixes exact Boolean source metadata, stronger than the generated
  canonical-result contract. Removing it now would lose that check.
- Root independently reviewed Astra's reverse emitter, fuel transport,
  interpreter assignment equation, tactic, shared canonical-fact extension and
  regressions: no semantic finding. The tactic constructs eventual witnesses
  from actual partial-correctness induction, without forward determinism or
  fuel monotonicity assumptions. Final exposure normalization avoids splitting
  arbitrary recursive field values; no proof-budget increase was needed.
  Reviewed source hashes: Reverse `fd75e97106b6ea14a0cb48cc7cbf36162b77331d6efbf032271da02cec4c059e`,
  RealizeFuel `c3d96d1fac416d514e87357a61b8a4ca60af3a12b93f9b67e4e69cf9efea1337`,
  RealizeInterp `3965512f1c2c91bf922d64954ad13953ba5bb4de71e99161b8d1e9ef29bab286`,
  tactic `c25f94fedbc4c4472be30020164dbe0202909d9ae97f958ef15f20b9f0ca14ed`,
  Normalize `bf8f86b91d7980e126850bd4b29ce4ff665bf760d250a7e7841389c61884e039`,
  regression `57b1ea1697689fe3e81d2db25696dc51e17101bff5d7e1608b4378540905f8d6`.
  Final focused tests passed; the final driver compiled all 18 production
  forward/reverse sidecars together with `--wfail`, exit 0, 41.680s (session
  68135). `.artifacts/n2-reverse/all-groups.{json,log}` records this check.
  Reverse claims use the exact closed renderer; production coverage checking
  and the full gate subsequently passed after builtin integration.
- Astra independently reviewed root's coverage/emission/manifest integration
  at baseline `56cf92c`, scoped diff SHA-256
  `e82879cb7c1230297c418c327fc76fb0f4431ca31da72e12b35d7b9df6b3e60c`:
  no findings. Forward/reverse frontiers remain separate; builtin contracts
  remain outside bodied denominators and do not enable callers implicitly.
  The builtin proof emitter itself and later checker mutations were outside
  that review and require separate final review. Seventeen Python adapter
  tests and focused direction tests passed before the combined gate.
- Root independently reviewed Astra's equality compatibility module and tests,
  SHA-256 `1a91425ca24dd0acf6314b0381a7154ff5e89e0197c93622f443a23b590070a3`
  and `da98e546aa35873bbfe03754ce2fc11bc46c39d5b62d6743d66e5b7dfe5a6a7a`:
  no findings. `ValueBEq` ties the actual dictionary to canonical source
  equality; lawful Lean equality requires a separate faithful encoder, while
  value-based equality permits non-injective encoders. List/option composition
  and actual generated `in_set` are checked, with no generic tuple claim.
  Focused `--wfail` session 18521 passed (662ms library, 488ms test), with
  exact allowed-axiom audits. Source-domain obligations remain independent.

- Astra independently reviewed Sol's final builtin emitter and selection tests:
  SHA-256 `29ae9d9b15d38da20679ddc1fab1ff242c2edc3b0a8bfd714a44cd0561bdedcb`
  and `f172cb16c4c6e678c8ee9c485948551475f3c3d1927216ac498f9d9606ecb9d4`.
  No findings: all 26 signatures, carrier/alias shapes, actual wrapper calls,
  raw type-argument order and shared exact statement renderers were checked.
  The empty generated print-hint table is required, and family-specific imports
  avoid unrelated rebuilds. Final focused author checks passed; production
  regeneration emitted all 78 audited theorems and the exact coverage checker
  passed `--wfail`, session 78265, 10.804s. Thirteen mutations rejected at their
  intended boundaries, including replacing a reverse/dispatch theorem with the
  same entry's forward theorem. The additional mutation code was independently
  reviewed at SHA-256 `775a3f90f8f37ca200123ff5f040cea1b6c68704ea7d52adf51079497032d703`.
- Three test-only builtin reverse theorems were removed after production checking:
  whitespace, distinctness and unsigned-bit conversion. Sol reviewed that their
  statements are subsumed by the generated `.realizes` certificates. Exact raw
  result checks, boundary failures and ordering/metadata regressions remain.
- Astra independently reviewed the final field-update consumer simplification
  at SHA-256 `20ae20c82b404c8be237a5b50c1d712c909cc56ce3ccc6689851d78589e4aec7`:
  no findings. All seven public theorem statement texts are unchanged; 34 private
  declarations with no external references were removed. The new proof combines
  generated reverse correspondence with the existing total update meaning,
  extracts sufficient fuel and rejects source errors through `ResRel`. The old
  private bound `7 * length + 33` is retired, not a retained public guarantee.
  Focused certificate session 89833 passed (497ms correspondence, 427ms
  certificate). Existing source/behavior/representation mutation boundaries
  remain; they do not independently replay a mutated reverse proof.

- Final independent consistency review by Astra found no findings, scoped staged
  diff SHA-256 `5bdeeae2d21f5353bfffbadf829f643319fae3c2e6ca3c0a6387118c398dc514`.
  Counts were recomputed directly: 350 declarations, 888 obligations, 139 bindings
  (18 forward + 18 reverse + 26 dispatch + 77 run-soundness), 749 unresolved.
  The 52 builtin invocation and two determinism claims do not inflate that
  count. Added modules are root-reachable and library boundaries remain intact.
  This review did not rerun builds; Sol's review owns the three test deletions.
- Full local `nix develop -c bash /Users/qobilidop/my/work/p4-spectec-lean/scripts/check.sh`
  passed with actual exit 0, session 60774, 74.570s, all 44 stages and no skips.
  Evidence `.artifacts/n2-full-gate.{log,json}` records tested index tree
  `0f249ebf77ef66a2dbe66232b409a422526816a8`. Libraries, all tests and examples,
  exact certificates/axioms, freshness, thirteen coverage mutations, consumer
  mutations, both typing replay legs, target/packet/verify observations and
  full-P4 census passed. This warm run is not a controlled speed comparison.
  Later checkpoint prose changes do not alter executable inputs. Remote CI is
  routine asynchronous follow-up; N2 remains open.
  Strict core completion was exercised separately and returned actual exit 1
  for incomplete certification, after its prerequisites passed. Evidence:
  `.artifacts/n2-strict-core.{json,log}`. The denominator and remaining obligations
  stay intact. Representation/equality support is committed as `c383ac7`;
  builtin-family and invocation contracts as `66f1253`.

#### Source-domain integration constraints

Read-only N2 analysis by Astra identifies the next implementation boundary:

- Guard-free and internal invocation paths do not establish input shapes.
  Actual source producers, initialization and prior successful operations must
  supply the independent grammar invariants. Runtime membership is not a
  substitute: numeric tags and optional shapes have checked counterexamples.
- The first actual representation SCC is `typeIR`, `parameterIR`, `fieldTypeIR`
  and `externMethodTypeDefIR`. It uses lists, source sets/pairs, text and Nat
  widths, with no optional or tuple fields and no runtime-only raw-extern
  alternative. An independently source-indexed grammar and sufficient-decoder
  induction can begin there, using actual quoted constructor signatures.
- Legal polymorphic equality requires `(x == y) = valueEq x y` where generated
  source helpers use `List.elem`. `LawfulBEq` alone is insufficient when the
  encoder is non-injective. Builtin set/map contracts already use canonical
  value equality; this additional law is needed for their source callers.
- The overlapping `ToValues` product instances distinguish an abstract product
  tail from a statically visible tuple. A generic product codec would hide that
  distinction. Use explicit source tuple arities; the first TypeIR SCC avoids
  this issue, while Var_init's transient iteration tuples have known arities.
- Type_eq and default use MixopSC; Type_ok's RecurseSC sites are numeric Nat
  checks, not recursive value-depth checks. The checked interpreter paths do
  not call the legacy total matching/substitution fallbacks found by the scan.
  Fixed checked-substitution fuel still needs a per-call syntactic-depth proof
  or a sufficient-fuel interface for arbitrary legal deep type instantiations.
  More invocation fuel alone cannot discharge this obligation.

These are retained constraints and an integration plan, not evidence bindings.

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
gate. Its temporary worktree was removed during handoff; the superseded branch
was removed after N1 integration. Historical artifact hashes, review limits and
recovery instructions remain in the pre-N1 version of this note at
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
The executable checkpoint `ccb88591b82c29fe334cb2dcc844e298eae5773f` is published.
[CI 36290248213](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36290248213)
succeeded on that exact revision with all 44 stages passing. Remote gate time was
8m33s; job time was 9m44s, including generated-library, certificate and native
rebuilds. These conditions differ from the local 104.859s warm-artifact gate.
N1 is closed. The obsolete local `wip/nano-reverse` branch was deleted after main
CI passed, and listing its name confirmed absence. One worktree remains; the
unrelated documentation branch is preserved.

This final closure update changes working-state prose only, reusing the unchanged
executable tree's local gate and CI evidence, with independent review and final
text/link checks. The final published documentation revision is also checked in
CI before the user-facing milestone completion report.

Independent read-only Sol closure review found no issues in the three-file diff
against `ccb8859`, SHA-256
`5668c5f399e1350a1235a22b4221e575a4b60fb8697e940542f9c07c53442175`.
The reviewer verified exact-code CI metadata, all 44 passing stages, timings,
branch absence and the one-worktree state. No builds were rerun for this prose-only
update; unchanged executable inputs retain the passing full local gate 40282.

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
