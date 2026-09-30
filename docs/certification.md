# Certification

What does a certificate from this project guarantee?

It connects a generated Lean definition to the meaning of its quoted
P4-SpecTec AL definition in our Lean reference interpreter, under explicit
input and environment assumptions. Certification happens when building the
language model, not separately for every P4 program that uses it.

A successful Lean build alone does not establish this connection. Nor does
a certificate prove that the reference interpreter faithfully implements
upstream OCaml or the intended P4 language.

## What is certified today?

Nano-P4 generates a Lean model with two-way AL correspondence for every bodied
definition, a concrete NanoSwitch target that discharges the core's extern
contract, and a two-way theorem composing semantic initialization with packet
processing. Both Lean paths match the pinned upstream verdicts, outputs and
packet sessions on the entire corpus. A whole-program certificate proves the packet
behavior of one exported program, `src-addr-filter.p4`, for a stated family of
packets, on both Lean paths. The combined completion check verifies every proof,
replay, consumer and sensitivity obligation of
[Design, section 9](design.md#9-nano-p4-scope-and-acceptance): the core and target
proofs, both replays, the whole-program example and distinguishing mutations across
layers, each rejected by a named check. The section's remaining requirements, an
independent review and exact-revision CI, are publication records rather than checked
evidence; the Nano-P4 milestone is complete for the one source tree whose record
contains both (see [Nano completion inventory](#nano-completion-inventory)). Full-P4
support is not yet a usable generated library.
The README gives the short project status; this guide is
the user-facing account of current capabilities and their guarantees.

| Artifact | Checked claim | Boundary |
|---|---|---|
| Generated Nano-P4 correspondence theorems | Every terminating outcome in either execution has a matching outcome in the other | The supported fragment and related inputs under explicit environment assumptions; source-domain coverage remains separate |
| Generated builtin contracts | Canonical outcomes of actual dispatch and generated wrappers agree; both invocation directions are checked | All 26 builtins on related inputs, with explicit type arguments and empty print hints where required |
| Field-update certificate | Both directions of executable correspondence, representation coverage and initialization; distinct-name update commutation transfers to reference executions | One helper on a declared scalar source domain, not arbitrary P4 assignments |
| Generated relation soundness theorems | Successful generated execution implies the generated logical relation | Does not by itself connect that relation to AL or prove every relational witness executable |
| [NanoSwitch extern discharge](../NanoP4Target/Contract.lean) | The typed extern instance and the registered reference target satisfy `externsContract` in both directions | Every related input, global context satisfying the specification and trampoline fuel; guards off |
| [NanoSwitch session composition](../NanoP4Target/Session.lean) | From `NanoSwitch_init` on a program through every packet, per-packet transmissions, forward/drop, final context and failure kinds agree in both directions | Related programs and arbitrary packet sequences; the pinned empty print hints; STF parsing and expectation matching stay upstream |
| [Source-address filter certificate](../ExampleProofs/NanoP4SrcAddrFilter/Certificate.lean) | Every three-byte packet on every host-range port is forwarded unchanged exactly when its source address is 1 or 2, shorter packets are dropped, on the generated model and the reference interpreter | One exported program; packets with a payload excluded; assumes `PacketStateText` |

The [generated coverage report](../NanoP4Spec/coverage.json) and its [refinement
index](../NanoP4Spec/Refinement.lean) record forward and reverse AL theorems for
all 153 bodied definitions at the current Nano-P4 pin. Extern-dependent theorems
assume the abstract `externsContract`, which `NanoP4Target.externsContractHolds`
discharges for the concrete target; a theorem whose callable closure reaches
`print_` also assumes `cfg.printHints = []`, the pinned hint table (the export
declares no print hints). Both reports come from the same generation plan. Separate source-domain certificates now also cover `ite`,
`repeat_`, `empty_set` and `empty_map`, under arbitrary legal parameter codecs
and independent admission predicates. The gate requires every core, target and
sensitivity obligation. These counts are not a percentage of P4 language
behavior certified.

Full-P4 production generation remains incomplete. Bounded stateful emitter
and proof fixtures do not constitute production full-P4 certification.
Generated reverse certificates construct finite reference executions using
outcome induction for recursive functions, including failures. They assume
related inputs and do not establish total termination. Separate generated
source-entry, codec and producer theorems establish source-domain coverage and
preservation for the selected fragment. The [handwritten regression](../P4SpecTecTest/Refine/NanoReverseExists.lean)
also checks exact Boolean result metadata. Generated relation certificates now
cover arbitrary admitted inputs for `Type_eq` and `ParameterType_eq`, including
ordered attempts and failure outcomes. Their logical relations retain separate
run-soundness claims; there is no blanket logical converse claim.

All 162 declared source type families have generated codecs proving encoding
validity, decoder soundness at any fuel and a sufficient bound for each source
value. This includes recursive syntax, nested containers and legal polymorphic
instantiations. The independent grammar follows source constructors: numeric
casts produce the declared numeric tag, and options use explicit absent/present
wrappers. It is deliberately distinct from permissive runtime subtype membership,
which can accept other raw shapes. Source input witnesses, successful output
preservation and actual intermediate call admission are separate checked claims.
The runtime-only raw extern alternative remains outside the declared `value`
grammar; the target's callbacks and receiver results are covered by the extern
discharge and session composition instead.

### Coverage metadata and checked evidence

`coverage.json` inventories the emitted claims. Schema version 3 records the library and export path, each callable's AL identifier and source
file, its recursive group and direct dependencies, theorem names and expected
types, and exclusions. The claim kinds and directions distinguish forward AL
refinement, reverse realization, builtin dispatch equality, generated-run soundness
and relation determinism, as well as source entry, output preservation and call
admission. Source type codecs have a separate namespace. Profile claims bind
primitive codecs, typed schematic-variable omission and actual table initialization.
Helper group theorems support these claims without duplicating the denominator.
Externs and builtins are dependency boundaries, excluded from the bodied denominator.

The report is metadata, not a certificate or a stored build verdict.
`check-coverage` regenerates it from the current export, requires an exact
match, then checks that every claimed declaration is a compiled theorem with
the expected type and only the allowed axioms. This also rejects omitted or
forged claims. Statement construction is shared with theorem emission; checking
does not independently prove that the generator chose the right contract.
Source identity still needs the separate freshness and quotation checks below.

The machinery belongs to `P4SpecTec`; the report belongs to the generated
library. Full-P4 will use the same machinery when production generation is
supported. Its capability census is an emission probe, not certificate coverage.
The stronger handwritten field-update certificate remains a separate consumer
artifact and does not increase the generated forward or reverse coverage.

### Nano completion inventory

The [completion inventory](../NanoP4Spec/completion.json) supplements callable
coverage with all 350 source declarations, including types and variables,
and the additional obligations in [Design section 9](design.md#9-nano-p4-scope-and-acceptance).
It references existing theorem claims rather than duplicating their statements.
The current 888 obligations have 767 compiled claim bindings. Source identity and
the 117 replay obligations are verified by the checker's own runs instead. The
whole-program consumer obligation counts only after `check-consumer` succeeds, and
the sensitivity obligation only after every mutation suite passes (see
[Distinguishing mutations](#distinguishing-mutations)). The bounded N2 check additionally requires the selected 30-definition
closure, all 162 type codecs, eight typed variables, all 26 builtin contracts,
primitive codecs and table initialization. It checks input coverage, output
preservation and full intermediate call admission separately. These counts are neither behavioral
coverage nor estimates of remaining effort. Even a definition with both directions
bound still needs its domain and environment obligations.

Dependencies conservatively combine the callable/SCC graph, named source-type
references (including notes), primitive/container representations and profile
prerequisites. They guide implementation; they do not prove semantic
composition or make an unimplemented contract checker available. Typing replay
belongs to the core stage; packet replay additionally belongs to the target.

The checker regenerates the inventory, checks source identities and the pinned
corpus, and invokes the existing compiled coverage and quotation checks. There
is no editable `checked` flag. Source identity and replay obligations are checked
by this CLI, not bound to compiled claims: it runs both typing replay legs and the
session replay and counts only the cases they verified. Target-stage obligations
bind handwritten `NanoP4Target` theorems, which `check-target` elaborates against
exact expected types and allowed axioms; the observations claim spells out its
observation relation. Printing binds the `print_` dispatch contract together with
the checked empty hint table of the pinned export.

Review and release are publication records, not kernel theorems or metadata verdicts.
The milestone's record, kept with the repository's working state for agents, names a
SHA-256 digest over every tracked file outside that working-state directory
(file bytes, link targets and submodule commits), the reviewed revision, the reviewer
and review verdict, and the successful full gate and remote CI run for that revision.
The checker counts the review and release obligations only when the current checkout
and the recorded revision both have that digest, so any later change to code, proofs,
documentation or pins leaves them pending until a new review and release are recorded.
A clone that lacks the recorded commit, such as CI's shallow checkout, cannot check the
record and counts nothing; the strict check is run in a full clone.
The review verdict and the CI conclusion are recorded observations; the checker does not
query GitHub.

The [corpus inventory](../P4SpecTecTest/Oracle/Nano/Certification/corpus.json) retains 78 programs
and 39 STF sessions. Upstream observations exist for every typing case and every
[STF session](../P4SpecTecTest/Oracle/NanoSwitch/Sessions/README.md): initialization,
then each packet's outcome, decision, transmissions and context. Stored observations
are inputs to replay, not proof that both Lean paths agree; the replays compare
them. All 78 programs and all 39 sessions (74 packets) match on both Lean paths.
Upstream reports session failures only as a class, and no corpus session fails,
so failure kinds are compared between the Lean paths, not against upstream.

Normal checking accepts an accurately reported incomplete inventory. The full
gate requires `--require-n2 --require-complete all --allow-unpublished`: it retains
the bounded N2 checks and rejects any missing obligation, except that review and
release records may be absent or describe another tree, since they are written
after a revision passes the gate and CI. Strict checking returns a nonzero exit
while its stage has unresolved obligations (`target` includes core prerequisites;
`all` includes the consumer, sensitivity, review and release). Without the
allowance, `all` passes exactly on a tree whose release is recorded:

```sh
nix develop --command python3 scripts/nano-certification.py --require-n2 --require-complete all --allow-unpublished
nix develop --command python3 scripts/nano-certification.py --require-complete target
nix develop --command python3 scripts/nano-certification.py --require-complete all
```

After changing source or evidence, regenerate metadata with
`python3 P4SpecTecTest/Oracle/Nano/Certification/corpus.py --update` followed by
`python3 scripts/nano-certification.py --update`, both inside the pinned shell.
Regeneration itself is not validation or certification.

Regenerate the Lean model from the repository root using the canonical relative
input argument:

```sh
nix develop --command lake exe p4spectec-gen exports/nano-p4.al.json --lib NanoP4Spec --runtime-extern value --update
```

The generator records that argument in generated headers. An absolute input path
changes otherwise identical files and triggers unnecessary proof rebuilds.

### Implementation boundaries

These limitations describe the implementation, not the intended design:

- Production stateful planning is rejected even though stateful interpreters,
  emitters and bounded proof fixtures exist. Fresh-state tests are not full-P4
  generation or certification.
- The NanoSwitch target ports extract, initialization and the packet driver;
  boot, STF parsing and expectation matching stay upstream, and a Lean session
  starts from the exported parsed program. Extern payloads are decoded from their
  compressed text, the identity runtime value equality uses (design section 5.3);
  replay, not a parser proof, shows that target-serialized payloads decode back.
  The shared verify helper retains upstream's full-P4
  calling convention, which does not establish Nano source-level support.
  Explicit `--runtime-extern value` generation adds a runtime-only alternative
  for raw extern callback results, preserving source quotations and membership.
  Checked [representation contracts](../P4SpecTecTest/Refine/NanoTargetRepresentation.lean)
  cover its codec, source packet/object separation, continuation interfaces and
  a paired source/generated receiver failure on a bounded runtime context.
  Actual short/full extract probes compare generated copy-in/out and receiver
  writes with the complete canonical reference context and exact fresh counters.
  Subsequent callee
  mismatch and the distinct direct-handler hard error remain observable; no PACKET
  wrapper repairs the receiver.
- [Unhinted printing](../P4SpecTec/Refine/Print.lean) preserves output and errors
  under canonical equality, through actual pure builtin dispatch and global
  lookup under explicit guard-free, empty-hint and environment assumptions.
  The quote checker verifies that both decoded and compiled Nano have empty
  print environments. General hinted-print
  correspondence remains open: equal canonical values can select different
  policies through their type notes. Builtin, cast, iteration and higher-order
  proof coverage must be read from the generated exclusions.
- Some legacy proof-facing matching/substitution helpers retain bounded-fuel
  false/identity fallbacks. Interpreter paths use checked APIs with explicit
  exhaustion and errors. Checked substitution uses a proved input-syntax bound,
  so it has no fixed syntactic-depth cutoff. Nonempty substitution through
  function types remains unsupported; the separate upstream type-fresh allocator
  is not modeled.
- Function-type comparison uses internal binder markers rather than allocating
  upstream type-fresh names. Its bounded comparison evidence does not cover
  later operations that could observe allocation history.

These exclusions prevent an end-to-end full-P4 claim. A consumer must use the
actual certificate's admitted domain and contracts, not assume that a callable
helper is covered by the translation proof.

## Reading a generated certificate

For a related reference input and generated input, a forward refinement
theorem says: if the reference interpreter finishes with a result at any
fuel, the generated definition produces a matching result. Success values
are related by the theorem's value relation; failures preserve their kind.
Exhausting the interpreter's fuel is not a semantic failure and imposes no
matching-result obligation. The theorem does not prove termination or
provide a reference execution for every generated result.

Check the actual theorem's hypotheses before using it. The current pure
certificates require dynamic guards to be disabled, no local function
overrides, and a global environment containing the quoted specification
(`HoldsSpec`). Their input relation (`Rel`) compares canonicalized runtime
values. It is not literal equality of all metadata, and does not justify
every observation, such as hinted printing.

There are further obligations when making a source-level claim:

- **Source identity:** the quotation must correspond to the intended export.
  `check-quotes` compares compiled Nano-P4 quotations with the decoded pinned
  export. The [comparison](../P4SpecTec/Codegen/QuoteCheck.lean) erases regions and hints
  and handles the eight typed schematic `VarD` declarations in a separate
  source-order comparison. A checked omission theorem proves that they leave
  initialization unchanged. Expression/path type notes, type origins, input
  positions and ordering remain significant. This is a runtime check, not a
  kernel proof of the exporter.
- **Representation coverage:** every input in the claimed source domain must
  have an appropriate generated representation. A theorem conditional on
  `Rel` alone does not prove that no relevant input was left out.
- **Environment and dependencies:** establish the theorem's assumptions for
  the actual initialized environment and account for the called definitions.
  An extern signature alone is not a semantic contract.
- **Observations:** state which values, failure kinds and state changes the
  claim preserves. Canonical equality alone is not a printing or packet
  behavior theorem without the corresponding observation contract.

The precise refinement statement and proof machinery are in
[Design, section 5.1](design.md#51-the-refinement-theorem).

## A complete bounded example

The [field-update certificate](../ExampleProofs/NanoP4FieldUpdate/Certificate.lean)
packages proof terms for the actual generated `update_fieldValue`, its quoted
definition, representation coverage, successful reference initialization and
both directions of correspondence. The reverse direction supplies finite
reference execution witnesses rather than assuming termination.

Its source domain is finite ordered field lists with exact byte names and
scalar W/S/B/MATCH_KIND payloads. Duplicates retain first-match behavior;
absent names leave the list unchanged. The domain is a shape restriction,
not a P4 typing or numeric-range theorem. Nested payloads, printing and
externs are excluded.

The [worked example](../ExampleProofs/NanoP4FieldUpdate/Example.lean) transfers
commutation of updates to distinct names, with already evaluated replacement
values, to reference executions. It does not justify reordering arbitrary P4
assignments whose expressions may have effects. The proof and its mutation
tests stay beside the example code.

`ExampleProofs` is a downstream example library, not reusable semantics or
proof infrastructure. It is excluded from the default `lake build`, but the
full gate explicitly builds it and runs its colocated tests. Reusable
libraries cannot import example or test-only modules; the gate checks that
boundary, including indirect local imports. Reusable initialization and
refinement support remain under `P4SpecTec.Refine`.

## A whole-program example

The [source-address filter certificate](../ExampleProofs/NanoP4SrcAddrFilter/Certificate.lean)
concerns the pinned upstream test program `positive/src-addr-filter.p4`: its parser
extracts the Nanonet header, and its table admits source addresses 1 and 2, denies 3
and otherwise runs no action. The program is not restated by hand. A generated
[quotation](../ExampleProofs/NanoP4SrcAddrFilter/Program.lean) of the exported AL value
is the input, and `check-consumer` checks it against the decoded export.

For every host-range port and every three-byte packet as the STF driver receives it
(uppercase hexadecimal text), the generated model with the concrete NanoSwitch target forwards
the packet unchanged on its port exactly when the source address is 1 or 2, and drops
it otherwise; every shorter packet is dropped. The other header fields are arbitrary.
`referenceFilter` carries the property to the reference AL interpreter with the
registered NanoSwitch externs: for every related program value, the reference
transmits the same at every sufficiently large fuel, and no terminating run at any
fuel transmits otherwise.

The theorems run the actual generated code, from `NanoSwitch_init` (typing, loading,
the evaluation context) through `extract` and the table. The `lazy_eval` tactic
computes them with kernel-checked proofs: it rewrites the generated recursive
definitions by their equations, keeps the other header fields symbolic, and decides
the unlisted source addresses with `omega` from facts about the byte's value.

The only assumption is `PacketStateText` (see [What remains trusted?](#what-remains-trusted)).
`check-consumer` also checks that the proven trace of the program's STF session, the
transmissions and the context after initialization and after every packet, equals the
pinned upstream simulator's recording. Colocated mutation tests show that a changed table
entry, a wrongly claimed branch, an extract writing reversed header bits, a wrong output
port and a changed recorded context are each rejected at their intended check (see
[Distinguishing mutations](#distinguishing-mutations)).

The receiver that extract returns is discarded when the parser returns, because the
parser only copies `packet_in` in; every corpus program extracts once, and a reused raw
receiver fails as a mismatch. No output or state of this program observes the receiver,
so its correctness rests on the extern contract, which relates the returned receiver at
every call, and on the target oracle's direct extract observations. A mutation whose
extract returns the packet state unadvanced still passes every claim of this certificate
and its trace, and is rejected by the extern contract.

Packets longer than the header (a payload), STF commands other than packets, and
other programs are outside this certificate.

## Distinguishing mutations

Mutation suites check that the certification rejects selected wrong artifacts at the
intended check. Each mutation of code is first shown to change a runtime result, so its
rejection is not mere proof-script brittleness. Each suite first passes unmutated, requires the named
diagnostic, and treats any other outcome, including a timeout, as a failure. The
completion check runs all three.

| Layer | Mutation | Rejected by |
|---|---|---|
| Generated code | The catch-all last alternative of `$expression_is_lvalue` tried first | Its generated forward refinement proof, replayed on the copy: the interpreter chooses an alternative the code does not |
| Generated code | A failed guard of that function made an error instead of a mismatch | The same replayed proof: the interpreter's failure kind differs |
| Generated code | `update_fieldValue` writes the old value | Its replayed refinement proof |
| Generated quotation | `DROP` omitted from the quotation of `forwardingDecision` | `compareSpecs`, the comparison `check-quotes` runs, against the decoded export |
| Generated quotation | A premise of `$expression_is_lvalue`'s quotation changed, or `update_fieldValue`'s identifier | `compareSpecs`; the refinement proofs, relative to the compiled quotation, cannot see it |
| Export | A print hint added to a copy of the pinned export | `check-quotes`' empty print-hint check; quotation comparison erases hints by design and still passes |
| Representation | A scalar encoded with the wrong tag | The field-update source-representation proof |
| Program identity | A changed table entry in the source-address filter's quotation | A copy of `check-consumer`'s identity comparison, and `nano-program-quote --check` itself |
| Target state | Extract writes the header bits reversed | The whole-program claim, by evaluation |
| Target state | Extract returns the packet state with its cursor unadvanced | The extern contract; the parser discards the receiver, so the certificate's claims still hold |
| Observation | A wrong branch or output port claimed; a recorded context replaced | Evaluation; `check-consumer`'s comparison with the upstream recording |

The code mutations run copies of the generator's output text and of its generated
proof in a scratch namespace, never hand-written variants. The suites live beside
their subjects: [field update](../ExampleProofs/NanoP4FieldUpdate/test/run.py),
[source-address filter](../ExampleProofs/NanoP4SrcAddrFilter/test/run.py) and
[cross-layer](../P4SpecTecTest/Oracle/Nano/Certification/mutations.py).

## What remains trusted?

| Boundary | What supports it | What is not proved |
|---|---|---|
| Lean proof checking | Kernel checking and audits permitting only `propext`, `Classical.choice` and `Quot.sound` | Correctness of the Lean kernel itself |
| P4-SpecTec source to exported AL | Pinned upstream parser, elaborator, algorithmization and JSON exporter | Preservation of source-language meaning by those stages |
| P4 programs to exported AL values | The pinned upstream P4 frontend and program exporter; `check-consumer` compares the quotation with that export | That the export is the program's meaning |
| Upstream observations | Pinned recordings of upstream typing verdicts and STF sessions, captured by repository scripts | That the capture faithfully records upstream behavior |
| Exported AL to Lean quotation | Decoding and `check-quotes` comparisons | Universal correctness of the exporter, decoder or quoting implementation |
| Lean reference semantics to upstream behavior | Side-by-side port review and differential tests, including builtin observations and every corpus typing case and STF session | General equivalence of the OCaml and Lean interpreters, complete extern coverage or device fidelity |
| Generated code to Lean reference | Checked correspondence proofs for the recorded fragment | Definitions and input domains outside the proved claims |
| Packet-state text round trip (`PacketStateText`) | Tests on sample states and every replayed corpus packet | That Lean's `partial` JSON printer and parser round-trip the driver's packet state; whole-program theorems assume it |

The reference includes the runtime helpers and builtin implementations it
uses. A certificate is relative to that reference, not an independent
verification of those implementations. Known port deviations are recorded
in [Design, section 5.3](design.md#53-deviations-forced-by-lean).

Whole-program theorems also assume `NanoP4Target.PacketStateText`. Extract decodes
the driver's packet state through the compressed text of its JSON, as the target
port identifies extern payloads by that text, and Lean's JSON printer and parser are
`partial`: no proof can compute the round trip. The premise is a hypothesis of every
theorem that runs extract, never an axiom.

The Lean executable toolchain is also trusted when running differential
tests, and the Python completion checker when it counts replay, sensitivity and
publication obligations. Passing tests is useful evidence about selected executions, not a
replacement for a theorem. Mutation tests check that selected incorrect
artifacts are rejected; they do not prove detection of every possible bug.

## Inspect and check

From the repository root:

```sh
nix develop --command scripts/check.sh
```

This is the same gate used by CI. It builds the Lean libraries and proofs,
checks generated-source and coverage freshness, theorem types and axioms, compares quotations,
runs differential tests and every mutation suite, and requires combined completion. A
passing gate means those recorded checks passed, not that every definition of full P4
has an AL correspondence certificate.

For a focused inspection, start at the generated refinement index or the
field-update `Certificate` structure linked above. Follow the actual theorem
types and proof dependencies, rather than inferring guarantees from a file
name. Targeted checks, after the normal build has prepared dependencies, are:

```sh
nix develop --command lake build NanoP4Spec.Refinement
nix develop --command lake build ExampleProofs.NanoP4FieldUpdate.Certificate
nix develop --command lake build ExampleProofs.NanoP4SrcAddrFilter.Certificate
nix develop --command lake exe check-quotes
nix develop --command lake exe check-coverage
nix develop --command lake exe check-coverage update_fieldValue
```

The optional AL identifier prints the entry's dependency closure and blockers
after checking the whole report. It does not discharge the theorem's input or
environment assumptions, or change an uncovered entry into a certificate.

These targeted commands do not replace the full gate. Changes to coverage
or theorem assumptions should update this guide with the code; detailed
theorem inventories and worked proofs remain in their own Lean modules.
