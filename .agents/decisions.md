# Decisions

Current cross-cutting choices and reasons. Updated 2026-10-06.
Rules belong in [AGENTS.md](../AGENTS.md), architecture in
[Design](../docs/design.md), and detailed constraints in the linked topic
notes. This register is not a chronological log.

## Scope and product (2026-09-26, M3 resumed 2026-10-04)

Keep AL as input, the handwritten Lean AL reference, and the generated model.
The bounded field-update consumer is complete; broader M3 is incomplete. The user
paused it on 2026-09-26 in favor of bounded requests and resumed it on 2026-10-04
(below). Work outside M3 still needs a newly agreed scope. Reason: demonstrate a
complete usable source connection without mistaking isolated generated/proof
fixtures for full-P4 support.

The next major milestone is complete Nano-P4 support and certification, with
core semantics and target composition as separate required acceptance stages.
[Design section 9](../docs/design.md#9-nano-p4-scope-and-acceptance) owns the
scope and definition of done. Reason: demonstrate the full architecture on a
bounded language before expanding production full-P4 support. The user
authorized each stage in turn (the scope, then N0–N2, N3 and N4 on 2026-09-26 to 2026-09-29,
and N5–N6 fully autonomously on 2026-09-30). The milestone closed on 2026-09-30 at `42ffad6`;
no further Nano work is authorized.
Use the model tiers in
AGENTS (small for bounded inventories, mid-tier for bounded implementation/tests,
strongest for difficult semantics/proofs and independent review), with explicit
ownership and one integrator. Confidence high in the milestone choice;
N1 settled reverse-proof and runtime-representation feasibility; N3 and N4 closed core
coverage and target composition, N5 the whole-program proof, and N6 release evidence.
Revisit scope only through an explicit design
decision, not by excluding difficult cases from coverage.

On 2026-10-04 the user resumed full-P4 M3 and authorized pushing it as far as possible
autonomously, with one standing instruction: on a performance bottleneck, pause and improve
performance first. The M3 exit obligations
in the [full-P4 overview](notes/full-p4/overview.md) are unchanged, and each stage still needs
its checks, independent review and recorded evidence. Consequential choices made without the
user are recorded here for later review.

The goal is a certifying compiler, technically a proof-producing semantics
translation, not a universally verified generator. Reusable models amortize
per-artifact checking and allow generator evolution. This is a tradeoff, not
a claim of general superiority over verified compilation.
[Discussion](notes/compiler-certification.md) retains the user-requested
rationale; [Related Work](../docs/related-work.md) owns sources.
Confidence high; revisit with measured scale or consumer evidence.

## Staged explicit-state generation (2026-10-04, completed for relations 2026-10-05)

A specification in explicit-state mode (one declaring `fresh_typeId`, so full P4) is planned
without the pure-mode certificates: types with codecs, subtype bridges, the `Externs` class,
executable functions, tables and relations, quotations, the logical relations (next entry)
and a run-soundness theorem for every relation. Every definition and type is listed in
`coverage.json` with the exclusion `Emit.statefulReason`; no refinement, representation or
initialization module is emitted. Reason: the certificate emitters are stated for the pure
ABI, and an all-or-nothing guard had hidden that the executable half elaborates for the
whole export (about 235 s cold, with native compilation) and agrees with upstream. Emitting
the executable library first gave a second Lean leg for corpus replay (M3C), and each
certificate family is a separately enabled stage with machine-readable exclusions.

The run-soundness rule the planner decides: a relation gets a `run_sound` theorem when every
relation its premises call outside its recursion group has one (functions it calls may be
recursive: their calls are run equations), by symbolic execution alone outside recursion and
inside the group's fixed-point induction otherwise ("Recursive state run-soundness by
fixed-point induction"). A group with a type-parameterized member, and every relation that
calls a relation without the theorem, gets a `runSoundness` exclusion with its reason; a
relation `StateProps` could not render would get a `logicalRelation` exclusion. No claim is
recorded for a relation without a theorem. All 256 full-P4 relations prove, each theorem is
a coverage claim, and `check-coverage --full-p4` checks the claims in the gate. The 2026-10-04
objection to "enabling bounded emitters for whatever they accept" (comment-only exclusions
would look like coverage) is withdrawn for `StateProps` and `StateRunSound`, which accept
everything, and still holds for `StateValidate`. Confidence high.

`P4Spec/` is generated, ignored and pinned by `P4Spec.manifest.json` (per-file SHA-256 and
size) instead of being committed: it is about 32 MB and one module is 6.7 MB, above the 5 MiB
cap. The gate regenerates, checks the manifest, builds and compares quotations. Cost: a
generator change shows as changed digests, not as a diff, so the commit message must say what
changed. Rejected: committing compressed generated modules (Lake cannot build them, and Git
history would grow by megabytes per generator change) and an exception to the size cap.
The user confirmed this on 2026-10-05 after a survey of prior art, with two refinements.
First, `P4Spec.samples/` commits byte-for-byte copies of a few small generated modules,
checked by the gate, so a generator change yields a readable diff. The set covers alias,
inductive and structure types with codecs and subtype bridges; recursive functions and a
table; a builtin wrapper; executable relations; logical relations with named attempts, an
iterated premise, a negative premise and a mutual group; and run-soundness of a single
relation, a mutual group and a group with the extern instance. Not covered, because the
smallest module holding them is too large or absent: the `Externs` class, auxiliary
predicates inside a mutual block, and mutual executable groups. Second, when a downstream
Lake package needs to import `P4Spec` through a Git requirement, the generated sources go
to a separate repository updated by CI from a pinned commit of this one: Lake builds such
a dependency from its Git sources, so ignored files cannot be required.

Prior art observed through GitHub on 2026-10-05, nothing more: `riscv/sail-riscv` removed
its prover snapshots (2025-03-10) and `opencompl/sail-riscv-lean` holds the generated Lean
in a separate repository updated by a scheduled workflow (from unpinned checkouts; pinning
is our addition); `hacl-star`, `fiat-crypto`, `sail-arm`, `Wasm-DSL/spectec` and
`leanprover/lean4` track generated output in-tree (`dist/`, `fiat-*`, `snapshots/`, golden
`TEST.md` files of up to 2.6 MB, `stage0/`). Measured here: one snapshot of the library is
1.7 MB as a repacked Git pack and the 37 commits touching `NanoP4Spec/` occupy 2.9 MB of
this repository's packs, so size alone would allow committing; the reasons not to are
unreadable 31 MB diffs, a module above the cap, growth with certificates, and no consumer.
Revisit at the first downstream consumer, if the library is split into smaller modules, or
if the samples stop catching what reviews need.

## Shape of explicit-state logical relations (2026-10-05)

An explicit-state specification's logical relations are emitted one module per relation
recursion group under `Refinement/Relation/`, importing the quoted spec and the modules of
the relations they call; the run-soundness theorems and their coverage claims are separate
modules under `Refinement/RunSound/` with the same grouping. A relation module holds
definitions only. Reason: all 256 full-P4 relations elaborate, so the gate builds every
emitted module (the manifest pins which exist; nothing separately asserts that none was
excluded), at a cost of about 200 s of cold build beside the chain for the relations and
400 s for the proofs.

Two encoding choices follow from measurements on full P4. An auxiliary predicate of an
iterated or optional premise joins its relation's mutual block only when it mentions a
relation of the recursion group, directly or through a nested predicate; otherwise it is
declared on its own beforehand. Reason: Lean's automatic constructions for a mutual block of
101 types did not finish in 13 minutes, and 83 of those were independent. Every complete
attempt but the last is a named `@[reducible]` definition of the relation's inputs, and a
constructor's rejected prefix applies those names. Reason: restating earlier attempts made
the text quadratic in the rules (30 MB, 93 to 95% repetition in the large groups). The
executable `R.run` still inlines its attempts; the soundness proofs name each attempt once
and compare a rejected alternative with it by unfolding. Rejected: making `R.run` call the
named attempts (the attempts would join every recursive `partial_fixpoint` group,
multiplying its size). Confidence high for both, now that every recursive group is proved
against the named attempts.

## Recursive state run-soundness by fixed-point induction (2026-10-05)

A recursive group's theorem is one induction over the group's least fixed point
(`state_run_sound_group`, `P4SpecTec/Tactic/StateGroupSound.lean`): a `partial_fixpoint`
group is `Lean.Order.fix F hmono`, read from the definitions' values, and
`Lean.Order.fix_induct` runs with the motive "below the fixed point, and every relation
sound". The joint statement is the conjunction of the relations' ordinary state
run-soundness statements; each relation's theorem is a projection, so recursive and
non-recursive relations have the same claim. Reasons for each part:

- **Not Lean's derived `partial_correctness`.** Its derivation fails ("please report this
  issue") for a definition with a long parameter list (`Copy_out_inner`, eight
  parameters; the `Expr_inst` group): instance resolution does not find the pointwise
  order of the function type. The tactic never resolves these instances; it reads them
  off the fixed point's own instance argument. Revisit if a toolchain bump fixes the
  derivation and the direct proof becomes a maintenance cost.
- **Only the extern instance is abstracted from a fixed point.** The tactic supports a
  fixed point whose leading arguments are in the theorem's context, which is what the
  generator produces: every parameter is rebound with `have`, so Lean finds no fixed
  parameter but the instance. A definition that passed a parameter on directly would have
  it abstracted, and the tactic rejects that shape by name.
- **"Below the fixed point" in the motive.** A rule states a rejected attempt, a negative
  premise or a function call over the final definitions, while a step sees approximants.
  Monotonicity of `F`, which Lean proved when it accepted the definitions, keeps one
  unfolding below the fixed point (`Refine/Fixpoint.lean`), and in the flat order a defined
  outcome below another is that outcome. A retained run equation moves to the final
  functions by the monotonicity solver the definitions were accepted with
  (`solveGeneratedMonotonicity`), once, when it is retained. The retired aggregate proved
  this per definition by a symbolic `StateRefines` congruence over the whole body and
  exceeded the heartbeat budget at `Cast_impl`.
- **Terms, not unification, where a type is as large as the group.** Admissibility, the
  split of the step and the componentwise order facts are built as explicit terms; their
  types differ from what an elaborator would compare only by unfolding the group's
  definitions. Elaborating them took minutes on a two-relation group.
- **The tuple order is Lean's.** A definition's position in the group's tuple is read
  from the projections in its value; it is not the source order.

Three rules of the symbolic execution that recursion and scale forced, each a correctness
matter as well as a cost:

- Alternatives are split by applying the rule lemma, not by `simp`: `simp` rewrote inside
  each rejected attempt (inlining `have`s), after which every comparison with the attempt
  a rule names was a structural unification of two different terms.
- A retained failure's computation sits behind a local definition, and an induction
  hypothesis behind `Refine.Kept`: the steps that simplify with every hypothesis otherwise
  rewrite a rejected attempt with facts of the selected path, or use the hypothesis as a
  rewrite rule and erase the facts obtained from it.
- A rejected-prefix premise is closed from the retained failures in order, each chosen by
  the state it starts at; a constructor search compared every failure with every attempt.

Confidence high for the method (fixtures for self-recursion, mutual recursion, a function
member, iterated and negative premises, the extern instance; and the full-P4 groups
recorded in status). Evidence and measurements are in `.agents/notes/full-p4/overview.md`.

## Corpus sweep beside the shard campaign (2026-10-05)

Full-P4 corpus evidence on both Lean legs comes from `Corpus/sweep.py`: parallel capture and
two protocol-identical workers, a summary accounting for every candidate, no durability
machinery. The shard campaign (`shard.py`: locks, fsync, resume, CLI parity, one leg, one
case at a time, 32 MiB) is kept unchanged as the stricter harness. Reason: the campaign's
serial design made a full run cost hours and had only ever covered four candidates; a
sweep that finishes in 20 minutes found the one real discrepancy (the missing
`static_assert` port) in its first run and can be rerun after every generator change.
Cached observations are keyed by pins, probe and limits; verdicts are never cached.
Rejected: parallelizing `shard.py` first (each process rebuilds upstream and Lake targets
in preflight, and its identity model assumes concurrency one), and treating agreement
between the two Lean legs as evidence (they share builtins and the placeholder port).
Confidence high for use as a feedback loop. Revisit by extending the shard campaign to
the generated worker and a larger bound when a durable, CLI-checked record is needed for
M3C's exit.

The sweep's case bound is 1 GiB, stated to the workers with `--max-case-bytes`; the worker
default stays 32 MiB. Reason: 81 candidates are larger only because the IL value JSON
repeats regions and notes on every node; four are 339 to 926 MiB. One candidate remains
above the bound and is reported as unobserved, never as agreeing.

The placeholder target is ported once (`P4SpecTec/BackendSim/Placeholder.lean`) and used by
all four full-P4 replay tools. The generated legs call it through value codecs around the
generated `$find_var_value_t`, as the NanoSwitch port's dynamic interface does, instead of
a second typed implementation. Reason: one mirrored implementation to audit against
`placeholder.ml`. Cost: the generated legs' externs are exercised through `toValue` and
`ofValue`, which the replay already depends on.

Rejected programs come from a second set of the same tool, `sweep.py --regression`:
upstream's `testdata/regression/{neg,pos,sim}/*.p4`, enumerated from the checkout that the
revision guard has matched to the pin, each with its digest in the cache identity and no
committed manifest. Reason: 37 small files of the pinned submodule need no inventory of
their own, unlike the p4c corpus with its exclusion manifests. In its place the sweep
fails on any directory entry the enumeration would not follow, on an unobserved
candidate, and on any status other than the one a program's group promises (`neg`
rejected, the others accepted, on both relations and both legs), so the set can neither
shrink nor turn pass-only unnoticed. Confidence high. Revisit if upstream's regression
set grows a structure the glob does not follow.

p4c's error tests (2026-10-06) are a third set of the same tool, `sweep.py --errors`, with
their own manifest (`errors.json`, built and checked by `inventory.py` beside the positive
one) so that the positive inventory's identity, and every cache and campaign record keyed
by it, is unchanged. Reason: the negative set has its own exclusion references and its
own expectation (upstream runs it with `-neg`), and a combined manifest would have
invalidated the shard identities for no gain. An upstream `abort` (any target-side error;
at this pin a failed `static_assert`) is now evaluated and matched only by a Lean hard
error at the same counter (`matched-abort`), not skipped as unsupported: the one error test
that aborts is the only upstream evidence for that branch of the port. Cost: a hard error cannot say
whether the port aborted or erred, which the status name records.

The regression sweep's mutation suite (`mutations.py`, 2026-10-06) mutates committed
sources and the regenerated generated module in place, rebuilds the one worker, and
restores the source byte for byte, requiring the rebuilt worker's baseline digest back.
Reason: a mutation of the generated code must reach the real worker through the real
build, and Lake's content-hashed artifacts make the restore cheap (one module and the
link). Rejected: scratch copies of the mutated definitions (the entry relations call the
originals by name, so only the entry could be mutated) and a second worktree with its own
build (a second cold build per run). Expectations are exact sets of programs and
statuses; two are derived from the observations by a stated rule (which programs
allocate, which are accepted) rather than listed, so a pin change does not silently
invalidate them. Confidence high. Revisit if a mutation needs a module early in the
generated chain, where the rebuild would dominate.

## Packet target ports, v1model and eBPF, and the session oracle (2026-10-07)

The first full-P4 packet target is a Lean port of upstream's v1model simulator under
`P4SpecTec/BackendSim/` (`V1Model/`, with `Hash`, `State`, `Table`, `Stf/` and the extended
`SpecImpl/` and `Core/Object`), generic in the effect carrier and in the spec it calls back
into through an explicit `Make.Spec` of function and relation trampolines, exactly as the
placeholder and NanoSwitch ports are. Both Lean legs run this one port: the reference leg
registers it as the interpreter's externs, the generated leg dispatches its callbacks by
name to the generated definitions through value codecs and makes its typed `Externs`
instance from the same dispatch. Reason: one mirrored implementation to audit against the
OCaml, and the two legs then differ only in the semantics they call back into. Rejected: a
second, typed implementation of the target for the generated leg (the NanoSwitch pattern,
whose contract proof is Nano's; two implementations to keep aligned with upstream) and
generating the target (it is OCaml, not AL). Cost: every callback on the generated leg
crosses the codecs, and the known `valueEq` slowness applies.

The reference leg's relation trampoline is tied as upstream ties its registered `call_rel`:
a `partial` definition in the oracle whose configuration registers the externs over the
very evaluator it defines. Reason: the interpreter's extern interface passes only a function
evaluator at each call (`Interp.Extern`), and widening it would change every extern-contract
lemma the Nano certificates state; the knot lives in test code and is fuel-bounded.

Sessions are observed by a probe that runs upstream's own `run_stf_test` with an observing
pipe and records events at the architecture's boundary, including the state before each
packet; the Lean replay runs the ported statement runner and compares every event, with
the serialized target state canonicalized (IL values inside extern payloads lose notes and
regions) before `Runtime.Value.eq`. Reason: upstream's statement runner is inside its
simulator functor and not observable statement by statement, while every state change it
makes is visible at the next packet; and a register holds IL values whose cache identities
and source regions are no more semantics inside a payload than outside one. Rejected:
reimplementing the statement loop in the probe (a copy of upstream's harness to keep
aligned) and comparing payloads as raw text (a false disagreement on every register
write). Limits recorded in the session README. Confidence high for the comparison; revisit
if a target keeps anything but IL values inside its payloads.

The eBPF simulator is ported the same way (`Ebpf/`), and the statement runner of
upstream's `make.ml` is ported once (`Stf/Run.lean`) over a record of a target's
architecture operations, upstream's `ARCH` functor argument; the probe is a functor over
either pipe, and the worker and sweep select the target by `--arch`. Reason: upstream has
one runner over three architectures, and a second copy would be the deviation. The PSA
target is not ported: upstream's own PSA simulator test selects no runnable pair at the
pin (its expectation file records 0 of 0, one excluded), so a port would have no
upstream evidence. Not covered either: upstream's five custom v1model sessions
(`testdata/custom`) and its p4testgen STF sets. Both sweeps match on every candidate
(219 v1model, 15 eBPF; corpus note, "Packet targets").

## Memoized relation runs as upstream's cache mode (2026-10-07)

In the explicit-state profile every generated relation call and every defined-relation
invocation of the interpreter's stateful carrier goes through `Prelude.memoRun`, which is
the call by definition and whose compiled implementation memoizes it: the key is the
identity of each live input object (the entry keeps the objects, so an address names one
value; for the interpreter's IL values the object is the value's payload container, which
`Runtime.Value.eq` identifies and which pattern binding shares where the value wrapper is
rebuilt) and the initial counter, and an entry is written only for a successful run that
moved the counter nothing, so a hit is what the run would have returned (for the
interpreter up to `eq` on notes and regions, as upstream's cache; its entries also record
the fuel, and a hit needs at least that fuel, since a run that succeeded under a bound
succeeds identically under a larger one). The table is a persistent hash map in a
module-initialized cell: the runtime never treats an object in such a cell as exclusive,
so a flat map would copy its buckets on every insertion; it is process-wide and keyed by
name, so the interpreter prefixes its names and a process runs one extern implementation
and one spec. Reason: upstream's
test configuration runs with its result cache on, and without one a rule group whose
earlier rules evaluate a recursive premise and fail late (`TableKeys_eval`, three rules
over a key list) costs time exponential in the list, which made 19 of the 219 v1model
sessions exceed an hour on both legs (`issue983-bmv2`, one packet, 13 keys, did not finish
in 12 minutes on either leg). Rejected: sharing the common prefix of consecutive attempts in
the generated code (changes counters when the prefix allocates, and every run-soundness
proof reads the complete-attempt shape); keying by value (hashing or comparing a context of
megabytes per invocation); a generator-level fixed-point restructuring (the group tactic
reads the fixed point from the definitions' values). The pure profile is untouched, so the
Nano certificates see no wrapper; the stateful tactics erase it by its defining equation.
Cost: a trusted `implemented_by` implementation, recorded in the certification trust table;
a process-wide table cleared at 256K entries, where upstream's evicts by a clock.
Confidence high in the transparency argument; revisit if a process must run two extern
implementations or two specs (key on their identity then), if a target keeps mutable state
outside the carrier, or if the pure profile needs it.

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

## Nano value domains and codecs (2026-09-26 to 2026-09-28)

Four choices about what the generated carrier holds and how source values are encoded.
The first and third concern the runtime-only alternative (`--runtime-extern`), which only
Nano uses; the codec and extern-domain choices bind every generated library.

- **Runtime representation.** Extract's raw `ExternV` result is preserved through an
  explicitly configured runtime-only alternative in the generated `value` carrier
  (`--runtime-extern value`); source quotations, `packetValue` and `objectValue` are
  unchanged, and the result is not wrapped in PACKET. The supplied subtype-check mode is
  followed as is: SkipSC is true, MixopSC matches source constructors, unsupported
  extension-sensitive checks reject generation; same-static-type casts preserve the raw
  value. Reason: the pinned guard-free semantics writes this value into the receiver;
  changing its shape would repair upstream behavior and change subsequent calls. The
  interface uses ordinary codecs and contextual contracts, with exact callback and state
  evidence separate from full target certification. Confidence high for this Nano
  profile. Revisit if a pin changes the callback result or subtype-check forms, or a new
  carrier needs a different runtime extension.
- **Declared source extern domains.** Opaque source declarations use the independent
  `ExternV` shape with arbitrary JSON, matching pinned upstream `runtime/value/match.ml`
  and the checked Lean membership rule; `Source.Valid.external` still requires an actual
  external source declaration. Using `False` would wrongly remove `objectState` and the
  PACKET alternative from the source domain. The runtime-only `value` alternative stays
  excluded from source admission. Opaque fields bind canonical extern codec dictionaries
  explicitly, also under reducible aliases. Confidence high (checked membership
  equivalence, the `objectState` codec, raw-extern rejection, hostile-instance
  regressions). Revisit if upstream changes opaque type membership; target-state
  invariants remain target contracts, not restrictions of core syntax.
- **Runtime-inclusive evaluation domain.** `Source.Valid` takes a domain of two parts,
  the opaque external-type domain and the runtime-only alternatives of declared types.
  The source profile (`externDomain`) has none, so grammar, codecs and statements are
  unchanged; the runtime profile (`runtimeDomain ["value"]`) admits exactly a raw `ExternV`
  at `value`. Evaluation-side claims (entry, producer, call admission) are stated over the
  runtime profile for callables whose domain involves the `value` closure, because after
  an extern callback the contexts hold raw values and source-domain preservation is false
  there; the runtime profile states the actual domain without assuming the target avoids
  raw values, which NanoSwitch does not. Types whose declared closure avoids `value` have
  the same values in both profiles (`Valid.runtimeIff`, from one checked closure
  certificate), so their source codecs lift. Rejected: a carrier-image domain
  (vacuous), a separate `RuntimeValid` inductive (duplicates every grammar lemma), owning
  the obligation in the target stage (the core call closure does not depend on the
  target). Confidence medium-high; revisit if a pin changes the callback result shape or
  another carrier needs a runtime alternative.
- **Nominal codec dictionary binding.** Closed nominal fields bind their source
  declaration's encoder and decoder with explicit parameter dictionaries, recursively
  through primitive, list and option fields; local type parameters shadow global names.
  Reason: reducible Lean aliases let unrelated later instances change a field's codec or
  add fuel layers (production recursive syntax exposed opaque encoder alias capture in
  initializer and selectCase fields). A declared alias retains one frame, not its old
  incidental minimum fuel. Contextual tuples have exact empty/two-field codecs; closed
  right products that would flatten, and unsupported arities, fail closed. Function-type
  dictionaries are unchanged pending separate support. Confidence high (hostile-instance
  and bound-name regressions, source-codec proofs). Revisit when tuple or function field
  support expands.

## Nano certificate shape and evidence (2026-09-28 to 2026-09-30)

The Nano milestone is closed (`42ffad6`); these choices still bind its artifacts and any
pure-mode generation. Detailed evidence: [nano certification](notes/nano-certification.md),
[nano release](notes/nano-release.md), [nano consumer](notes/nano-consumer.md).

- Generated relations try complete rule-path attempts in the reference's flattened order,
  each repeating its group's input match and shared premises, as `invoke_defined_rel`
  does. Reason: correct by construction; alternatives pair one to one. The earlier
  shared-prefix form was observationally equal but needed distribution through
  destructuring matches in every proof. Cost: shared premises run once per attempted
  path. Revisit only with a proved distribution lemma for every prefix form.
- Certificates of definitions whose callable closure reaches an extern relation quantify
  the generated `Externs` instance and assume one contract, `externsContract cfg`: for
  every global context satisfying the specification with every defined function's type
  parameters fresh, every fuel and related inputs, every configured callback outcome has a
  related generated outcome and conversely, with failure kinds preserved. The callback
  receives the interpreter's function evaluator at the remaining fuel, not a fixed
  trampoline (a fixed one made reverse correspondence unprovable for a target that calls
  back), and the target's callees need the same type-table freshness their callers
  carry, so callers of an extern gained the `X` hypothesis, discharged by the initialized
  environment. `NanoP4Target.externsContractHolds` discharges it for the concrete target.
  Revisit if a target needs builtin registration, a callback-free ABI, or output
  invariants a caller needs.
- A certificate module keeps the 4M heartbeat default; a group theorem adds 1M per source
  rule path or clause of its members (and, in explicit-state mode, a joint theorem has 4M
  per relation). Reason: cost grows with the paths explored, and a fixed budget either
  fails large definitions (`bin_op`, 26 clauses) or leaves small ones loose. A budget is a
  resource limit, not a weakened statement. Revisit with measurements or if a budget masks
  a runaway tactic.
- Generated `#audit_axioms` commands sit at the end of their namespace or section, ahead
  of any `mutual` block (`Emit.hoistAudits`, validated in `770e405`): an audit placed
  after its theorem waits for the proof and serialized a module Lean otherwise elaborates
  in parallel. Since 2026-10-05 one command may audit several theorems with one
  traversal; the single-name layout is unchanged for Nano. Tools that pair audits with
  theorems (`replay-cert.py`, the field-update mutation runner) follow this layout.
  Revisit if Lean exposes per-declaration asynchronous audits.
- Forward and reverse certificates have independent per-group dependency chains, with
  the old module names as import-only aggregates, so a caller waits on its own direction.
  Replay expands aggregates to the proof sources; timing an aggregate measures no proof.
- Native tactic execution is opt-in for scratch replay (`--native`); the core shared
  library is not attached to Nano's library configuration, because Lake puts native
  artifact hashes in every module's trace and a Codegen edit would rebuild every proof.
  Revisit a separate native tactic artifact only if repeated measurements justify its
  build boundary and maintenance cost.
- Completion: the gate requires `scripts/nano-certification.py --require-complete all
  --allow-unpublished`, which excuses only the review and release records. Source identity
  is discharged by the CLI's own checks (pins, export digest, generated freshness,
  `check-quotes`, `check-coverage`), recorded as `checkedBy`, never as a compiled claim.
- Target: `NanoP4Target` is a reusable library over the generated model that neither
  `P4SpecTec` nor `NanoP4Spec` may import. Completion binds target obligations to
  handwritten theorems only through `check-target` (exact expected types, axiom audit),
  because design section 9.4 requires a completion check that rejects missing target and
  replay evidence and metadata cannot certify itself:
  the extern discharge, an inhabitation witness for the assumed reference configuration,
  initialized two-way session composition, and session observations with the observation
  relation spelled out. Printing binds the `print_` dispatch contract plus the checked
  fact that the pinned export declares no print hints. `referenceSession`/`session` are
  pinned by name and by the corpus replay; replay obligations count only when the CLI's
  own run verified them. Session
  observations store values once with cache identities zeroed. Revisit if a corpus session
  fails upstream (failure kinds are not recorded) or a target needs STF commands beyond
  `packet`/`expect`.
- Whole-program statements are proved on the generated model by `lazy_eval`
  (`Tactic/LazyEval.lean`) and transferred to the reference by the session
  correspondence, never by evaluating the reference (its tables are hash maps and the
  generated recursion is `partial_fixpoint`; only the generated code has unfolding
  equations). Rejected: fuel twins of every generated function (a second, unchecked copy
  of the semantics, and no symbolic inputs), `simp` evaluation (evaluates every branch
  eagerly and loops under binders), and enumerating packets (2^24 header values). Every
  definitional gap abstracts the fixpoint constants on both sides (a test keeps the
  regression); symbolic inputs are temporary axioms inside `withoutModifyingEnv`. Revisit
  if a larger program needs caching across theorems or Lean exposes reducible fixpoint
  unfolding.
- Extract decodes the driver's packet state through the compressed text of its JSON, and
  `Lean.Json.compress`/`parse` are `partial`; `NanoP4Target.PacketStateText` states the
  round trip for host-range packet states as a named premise, never an axiom; runtime
  tests and every replayed corpus packet exercise it. Rejected: replacing the runtime's
  text comparison with total JSON functions (changes every canonical-equality proof and
  the reference port's observations for one premise) and a universal JSON round-trip
  premise (broader than the driver's states). Revisit if the port adopts total JSON
  printing and parsing, which would let the premise be proved.
- The consumer example (`ExampleProofs/NanoP4SrcAddrFilter/`) covers every host-range
  port with every three-byte packet and every shorter packet; packets with a payload are
  its stated scope limit (symbolic bit-array sizes). `check-consumer` binds it to the
  export and the pinned upstream session. Its `Program.lean` stays inside the example
  until a second program is quoted.
- Review and release are publication records in `notes/nano-release.json`, keyed to a
  SHA-256 digest over every tracked file outside `.agents/`; the completion check counts
  them only when the checkout and the recorded revision both have that digest (a digest
  cannot be carried forward to an unreviewed tree) and rejects a matching but incomplete
  record. Reason: a revision cannot contain its own CI result, and excluding `.agents/`
  lets the evidence commit record them without changing what was reviewed and tested; the
  CI conclusion is a recorded observation. Rejected: a commit-tree digest (every evidence
  commit would invalidate it), an unconditional gate requirement (every later change
  would fail until re-released), and querying GitHub from the checker (network and
  credentials in the gate). Revisit if releases become frequent enough to automate the
  record.
- Cross-layer sensitivity uses `$expression_is_lvalue` for ordering and failure-kind
  mutations (its catch-all last alternative makes order observable); `update_fieldValue`
  carries no ordering mutation because its alternatives have mutually exclusive guards,
  so swapping them is behavior-preserving and a rejection would only show proof-script
  brittleness. Each code mutation must also change a runtime observation; the completion
  check runs every mutation suite, and the gate no longer runs them separately.

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
