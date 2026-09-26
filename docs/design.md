# p4-spectec-lean: design

Status: agreed design, 2026-09-24; revised 2026-09-25 after a prior-art
review (section 11) and again at the end of M1 for what building the
pilot taught (the AL as the export, fuel, module grouping, the naming
rule). The compiler input and the reference interpreter are AL, the
algorithmic representation produced from IL by upstream's `algo` pass.
Section 3 distinguishes these stages and their historical names. The
2026-09-25 architecture discussion settled the direction and correctness
target in sections 1.1 and 5: retain the AL backend and prove one complete
consumer example before broader expansion. That bounded field-update
example is now complete; broader M3 remains paused and incomplete.

## 1. Goal and thesis

A compiler from P4-SpecTec's AL (algorithmic language) to Lean 4, written
in Lean and reusing upstream's OCaml frontend, elaborator and
algorithmization pass. Its goal is a usable P4-specific Lean library
whose executable behavior is connected by checked proofs to an explicit
AL reference semantics. A small P4 primitives library is planned for
downstream verification projects.

**Thesis.** AL already exposes executable dataflow. This makes it a
practical starting point for generating functions and logical rules,
while a handwritten AL interpreter in Lean supplies the reference for
translation certificates. The benefit of the generated interface must
be demonstrated by a consumer proof; execution speed is an unmeasured
potential benefit, not a delivered claim. The
[prior-art comparison](prior-arts-comparison.md) distinguishes this
approach from IL-to-prover generation and other certifying compilers.

> We aim to generate a usable Lean model and prove that it implements
> our explicit AL reference semantics, for a documented supported domain.

**Targets, not blanket current guarantees:**

| Target | Evidence required | Current boundary |
|---|---|---|
| Complete rendering | every definition of the pinned specification generates and kernel-checks, with no generated `opaque`, `axiom`, `sorry`, or `partial`, and all existing axiom/build gates | Nano generates; full P4 remains in progress |
| Agreement with upstream | differential verdicts and outputs under matched configurations, with exclusions explicit | recorded Nano typing corpus, bounded builtin/state and packet/driver observations; no complete target or whole-corpus result |
| Translation correctness | same terminating observable behavior in both directions, with representation and environment obligations, composed from definition certificates | generated AL certificates cover 18 Nano functions in one direction; handwritten field-update proofs establish both directions on a scalar source domain |
| Proof usability | a useful consumer theorem transferred through a complete certified dependency chain | bounded field-update commutation transferred to reference executions; broader public proof interface remains open |

The project keeps its semantic scope independent of any one consumer.
Consumer proofs inform the interface and establish its usefulness
(section 9); upstream adoption is not a success criterion.

### 1.1 Agreed direction and first consumer checkpoint

Retain AL as input, the handwritten Lean AL interpreter as the reference,
and the generated P4-specific model as the consumer interface. Do not
build an IL backend or undertake a broad redesign now. The current
statement-by-statement logical encoding is an implementation baseline;
its suitability as the long-term proof API remains to be demonstrated.

The first acceptance checkpoint required one small, useful example joining
the correctness argument to a downstream theorem, identifying:

1. A pinned source definition or entry point and its dependency closure.
2. The supported input representations, environment, execution mode,
   extern assumptions, and observable outcomes.
3. Both directions of executable correspondence described in section 5,
   with the required representations and dependencies covered.
4. A consumer property stated through the Lean interface and transferred
   to the corresponding reference executions.

The checked [field-update example](../NanoP4Proofs/FieldUpdate/Example.lean)
now meets this bounded checkpoint. It connects the actual generated
`update_fieldValue` to the quoted AL reference, discharges representation
and initialized-environment obligations, and transfers distinct-name
commutation for already evaluated replacement values. The scalar source
domain includes W/S/B/MATCH_KIND payloads and ordered finite field lists;
duplicates retain first-match behavior and absent names leave the list
unchanged. Reference realization supplies finite fuel, not a termination
assumption. The domain is a shape profile, not a P4 typing or range theorem.
Nested payloads, printing, externs and arbitrary assignment reordering are
outside this consumer claim.

This success is not certification of all Nano-P4 or full P4. Existing M3
work and correctness gates remain; broader expansion is paused.

Use the result to decide what abstraction lemmas or public proof interface
are needed. An IL-oriented interface or interpreter-only alternative can
be revisited if the example exposes a concrete problem; neither is a new
backend commitment or the next implementation task.

## 2. Principles

### 2.1 Correct by construction first, proofs second

Mirroring makes the manually ported reference semantics easier to audit
and maintain. It is a trust-management practice, not a proof that OCaml
and Lean behavior agree. Translation certificates and differential tests
provide separate evidence. Concretely:

- **The IL deep embedding mirrors `ast.ml` exactly.** Same type names,
  constructor names, constructor order, field order, and comments. One
  Lean file for the one OCaml file, at the OCaml file's path under
  `p4spec/lib/`, capitalised: `P4SpecTec/Lang/Il/Ast.lean`.
- **The semantics port mirrors the AL interpreter's structure.** One Lean
  module per OCaml module (`ctx.ml`, `interp.ml`, `backtrack.ml`,
  `nondet.ml`), functions with the same names in the same order, each
  citing the upstream file and line. No refactoring into a preferred
  shape.
- **Builtins and targets mirror their OCaml files**, one Lean file per
  file under `interface/builtin/` and `backend-sim/<target>/`.
- **Generated modules mirror upstream spec files**, one Lean file per
  `.watsup` file with the same name and directory, so a reviewer diffs
  `5-typing/5.10-typing-statement.watsup` against
  `P4Spec/5-typing/5.10-typing-statement.lean` (module
  `P4Spec.«5-typing».«5.10-typing-statement»`).
- **Generated names derive from spec names by one documented, invertible
  rule.** No renaming for taste.
- **Codegen output is boring on purpose.** No IL-to-IL rewriting passes,
  no rule merging, no cleverness. Per-construct encodings (section 5.4)
  are the only transformations, and they are listed.
- **The export is upstream's own serialization.** The IL types already
  derive JSON; the patch calls it.
- **Deviations forced by Lean are one named list** (section 5.3).
- **Mechanical mirror checks where cheap.** Scripts compare constructor
  and function lists between the OCaml and Lean files.

### 2.2 The repository is the only state

Work must be resumable by a fresh agent or person from the repository
alone. Conventions in section 8.

## 3. Upstream facts the design relies on

Source: https://github.com/kaist-plrg/p4-spectec and the P4-SpecTec paper
(arXiv 2608.00639).

### 3.1 Representations and the compiler boundary

There is one representation currently named **IL**, within a pipeline of
five main specification-language representations:

| Stage | Name | Purpose |
|---|---|---|
| EL | External language | Parsed `.watsup` syntax, close to the author's notation. |
| IL | Internal language | Elaborated, type-checked syntax with inferred information and type annotations. |
| AL | Algorithmic language | Binding analysis and side-condition insertion organize rules into executable matches and paths. |
| SL | Structured language | Rules become structured instruction blocks, including branches, bindings, relation calls and returns. |
| PL | Prose language | The structured algorithms acquire annotations for rendering readable specification prose. |

The pinned upstream implementation is explicit:

```text
.watsup → parse → EL → elaborate → IL → algo → AL → structure → SL → annotate → PL
                                             │
                                             └→ JSON → this compiler → Lean
```

The authoritative pipeline is `p4spec/lib/pass/pass.ml`. Its `algo` pass
is `Binding.Analyze.analyze_spec` followed by
`Sidecondition.Guard.insert_spec` (`pass/algo/algo.ml`). Most AL types are
aliases of their IL counterparts: expressions, types, values, premises
and function clauses are shared. AL changes the representation of rule
groups, table rows and enclosing definitions. SL introduces instruction
constructors such as `IfI`, `CaseI`, `LetI`, `RuleI` and `ReturnI`.
`lang/xl/` contains shared components, not another pipeline stage; `OL`
under `pass/structure/` is an internal representation of that pass.
These are representations of the *specification*. They are separate from
the P4 program IR whose semantics the `.watsup` files define.

Historical names explain some inconsistent references. Upstream commit
[`80b246ed`](https://github.com/kaist-plrg/p4-spectec/commit/80b246ed),
2026-06-29, renamed the old **IL to AL** and the old **IL2 to IL**.
The pinned upstream README still describes a pipeline without AL and
shows `-il` commands. The P4 command at the pin uses `-al`; the Nano-P4 run
command retains `-il` for its AL interpreter. This project's older use
of "IL to Lean" likewise names the language family too loosely: the
actual exported artifact is `*.al.json`.

AL is the chosen boundary because it keeps the inference-rule structure
needed for the generated `Prop` relations while already exposing the
execution structure needed for their run functions. Its upstream
interpreter provides both an executable oracle and a concrete reference
implementation to port to Lean. Consuming IL directly would require us
to reproduce algorithmization or formalize and validate another route
through binding and side conditions. Consuming SL would put the later
structuring and control-flow optimization passes inside our trusted
pipeline and make the connection to individual inference rules less
direct. The Nano-P4 experiment supports this engineering choice; it is
not a proof that AL is the only suitable boundary.

The refinement theorems start at **AL**. We trust parsing, elaboration
and IL-to-AL algorithmization; we do not prove their preservation of the
source specification's meaning. The IL AST and decoder exist because AL
shares their types, not because a direct IL backend is implemented.
Direct IL input is not a scheduled milestone. A future verified or
validated IL-to-AL pass could strengthen this boundary while reusing the
AL-to-Lean backend.

### 3.2 Facts at the upstream pin

- Pipeline: `.watsup` spec files → EL (parsed) → IL (elaborated) → AL
  (algorithmic) → SL (structured) → PL (prose). We consume AL: the IL after
  the algo pass (`pass/algo/`, binding analysis and guard insertion), whose
  types are the IL's except that rule groups are split into a shared match
  and rule paths (`lang/al/ast.ml`). In the AL every binder pattern is a
  variable, a tuple, a single case or a struct; subtype injections are
  explicit premises (`if e <: T`, `let x = e as T`); joint iterations carry
  length guards. That is what makes the spec algorithmic, and what the AL
  interpreter runs.
- The IL AST is `p4spec/lib/lang/il/ast.ml`, 261 lines. Definitions are
  type defs, functions with clauses and premises, relations with rule
  groups, plus `extern` types/relations/decs, `builtin` decs, and tables.
  All but `def` and `spec` already derive JSON serialization.
- Every relation carries an input hint. Elaboration and algorithmization guarantee all outputs
  are computable from inputs with no existential search. Determinism is
  validated dynamically, not statically, so rule order matters for the
  executable encoding but not for the `Prop` encoding.
- Externs and builtins are declared but not defined in the spec. Targets
  (v1model, PSA, eBPF) supply them; upstream keeps them in OCaml under
  `p4spec/lib/backend-sim/`.
- Size: 28,862 lines of spec, 591 syntax definitions, 253 relations,
  1,090 rules, 561 function declarations (paper, section 8.1). Nano-P4,
  the GSoC educational dialect, is the pilot target: 3.8k lines in 34
  files (`pacokwon/nano-p4-spec`), 161 types, 76 functions, 77 relations
  after elaboration. Its frontend, corpus (78 programs) and nano-switch
  target live on P4-SpecTec's `gsoc-nano-spec` branch, which is the pin.
- Upstream has three interpreters: AL (backtracking over IL rules, 64 KB,
  the faithful semantics), SL (87 KB), PL (90 KB). We port AL.
- Upstream's P4 frontend (`p4spec/lib/interface/p4/`) preprocesses, parses
  (Petr4-derived menhir grammar), and "boots" the program into an IL value.
- Upstream ships an experimental meta-circular spec (`spec-meta/`, ~65 KB):
  SpecTec's own semantics written in SpecTec. Not relied on; noted as a
  possible future source for the IL semantics.
- Upstream maintains `excludes/` lists of p4c programs it cannot handle,
  with reasons; the differential harness reuses them.

## 4. Architecture

### 4.1 Spec flow

```
OCaml (upstream, unchanged)                Lean 4 (this repo)
spec files → Parse → Elaborate → IL → Algo → AL ──┐
                                                  │ algo -json  (our only patch)
                                                  ▼
                              p4.al.json ──decode──▶ P4SpecTec.AL over P4SpecTec.IL
                                                            │
                                                            ▼
                                                   P4SpecTec.Codegen  (lake exe p4spectec-gen)
                                                            │ writes one .lean per spec file
                                                            ▼
                                                   P4Spec/<Section>/<File>.lean  (committed, diffed in CI)
                                                     types      inductive / structure / abbrev
                                                     functions  plain def or partial_fixpoint
                                                     relations  inductive R : Prop + executable R.run
                                                     ⌜d⌝, refinement theorems, lemma library
                                                     class Externs  (external operation signatures)
                                                     ▲ imports P4SpecTec.Prelude
                                                     ▲ instantiated by P4Spec.Targets.*
```

Decisions:

- **Almost nothing in OCaml.** The JSON dump is a small patch to upstream.
  Everything else is Lean, including the compiler: the IL deep embedding
  must exist in Lean for validation anyway, so the generator and the
  validator share one AST and one decoder. The emitter uses `Std.Format`
  and Lean's token table for formatting and keyword escaping. This is an
  engineering choice, not a claim that an OCaml generator cannot be verified.
- **The compiler takes an AL JSON export.** Upstream prepares that export
  from specification files; a consumer can include an architecture or a
  contract written in SpecTec in the upstream input.
- **Text emission, one module per upstream spec file.** The generator
  prints `Std.Format` with its own printer at 100 columns and writes
  ordinary `.lean` files that Lake builds like any other module; keyword
  escaping uses Lean's own token table. A recursive group that spans
  files is emitted in the module of the last file (section 5.3), so a
  spec file whose definitions all belong to such groups gets no module
  of its own (7 of Nano-P4's 34 files). The files are
  committed; CI regenerates and diffs them, and `--update` refreshes
  them. This gives Lake parallelism and incremental builds, keeps the
  IDE responsive, makes every codegen change a reviewable diff, and
  keeps generated files mirroring their sources. Every prior art emits
  text; Wasm's monolithic outputs are the scale warning.
- **Recursion strategy (M2).** Every generated definition is written in
  the monad `Eval := ExceptT Fail Option` (`Prelude/Eval.lean`): failure
  is data (`Fail.err`, `Fail.unmatch`, upstream's `Err` and `Unmatch`),
  divergence is `none`, and sequential choice `Eval.orElse` retries only
  on `unmatch`, as upstream's `choose_sequential` does, which makes it
  monotone. A recursive group is defined by `partial_fixpoint`, which
  yields unfolding equations and the `partial_correctness` induction
  principle the soundness proofs use; for that principle a definition's
  type is `Option (Except Fail T)` and its body `ExceptT.run` of the
  `do` block, with calls lifted by `ExceptT.mk`. Non-recursive
  definitions are plain `def`s. Structural recursion is not used even
  where it would work, so every group has the same proof principle. M1
  used explicit fuel; no fuel remains. Never `partial`.
- **Relations are emitted in both encodings** from one compilation of
  the rule paths: the executable function `R.run` from the inputs the
  hint names to the outputs (M1), and an inductive `R : args → Prop` in
  notation order with one constructor per rule path (M2). The
  constructor's implicit arguments are the variables the path binds; its
  hypotheses are the path's statements in the same A-normal form as the
  run function (a hoisted call is `f args = some (.ok x)`, an `if` is
  `e = true`, a rule premise is the relation applied, an iterated premise
  is a pointwise fact along the zip of its lists); pure bindings and
  pattern matches are substituted. Each relation gets the theorem
  `R.run_sound : R.run i = some (.ok o) → R i o`, proved by the generic
  tactic `run_sound` (`P4SpecTec/Tactic/RunSound.lean`): a symbolic
  execution of the run function with the `Eval.run_*` lemmas, the
  induction hypotheses of `partial_correctness` for the group's members,
  the earlier `run_sound` theorems for other relations, and the
  constructor of the rule path taken. A recursive group's theorem comes
  from Lean's `mutual_partial_correctness` through `run_sound_group`,
  which matches the principle's conjuncts to the generated statement by
  their function, since Lean orders the members of a group in its own
  way. Every generated theorem is followed by `#audit_axioms`
  (`P4SpecTec/Tactic/Audit.lean`), which fails on any axiom outside
  `propext`, `Classical.choice` and `Quot.sound`.
- **Extern signatures become fields of a generated class.** Bounded dynamic
  Nano target/driver ports exist, but a complete generated typed target
  implementation remains open. Builtin declarations get generated wrappers
  over the handwritten primitive library. Signatures alone are not semantic contracts; a complete
  example must discharge or expose the relevant implementation assumptions.

### 4.2 Program flow

The spec files describe the P4 *language*. An individual `.p4` program
is parsed and represented as data. Its program JSON is distinct from
the specification's AL JSON. The compiler generates the language model
once; it does not generate a new Lean function for every P4 program.

The current Nano-P4 typing harness has two paths:

```text
prog.p4 → upstream preprocess/parse/boot → program JSON → generic program value
                                                               │
                         ┌─────────────────────────────────────┴──────────┐
                         ▼                                                ▼
              decode as NanoP4Spec.program                     Lean AL interpreter
                         │                                    + loaded AL specification
                         ▼                                                │
              generated Program_ok.run                        interpret "Program_ok"
                         │                                                │
                         ▼                                                ▼
                    typing result                                   typing result
```

The runners are `P4SpecTecTest/Diff/NanoP4Run/Main.lean` and
`P4SpecTecTest/Diff/NanoP4Interp/Main.lean`. The latter reads
`exports/nano-p4.al.json` and initializes the handwritten interpreter
before applying the rules to program values. It does not import the
generated Nano-P4 library. Bounded packet and driver replay starts from
upstream-captured booted inputs; it is not a Lean boot/STF implementation
or a complete architecture/extern path.

- No P4 parser in Lean. The grammar is large, has a C-style preprocessor,
  and upstream's parser is the one the differential tests trust.
- A shallow embedding (P4 program → Lean functions) would be a separate
  later compiler, proved correct against this semantics. Out of scope.

### 4.3 Why retain both execution paths?

The handwritten interpreter in `P4SpecTec/Interp/InterpAl/Interp.lean`
defines the reference meaning of supported AL. The generated functions
provide a P4-specific interface intended to be convenient to run and
reason about. Correspondence proofs connect them; one interpreter alone
would suffice to execute programs, but would not provide that generated
interface. The consumer checkpoint tests whether the interface earns
its additional compiler and proof machinery.

The compiler emits `.lean` files, including theorem statements and proof
scripts. A separate Lean build executes handwritten proof automation and
checks the resulting proofs. These proofs are not recomputed per program
or packet. Both execution paths use manually implemented support code;
agreement between them is not independent proof of the reference's
fidelity to upstream or to intended P4 behavior.

## 5. Verification and validation

**Correctness target.** For the declared supported inputs and corresponding
environments, the generated executable model and the handwritten Lean AL
reference have the same terminating observable behavior. This requires:

- Reference-to-generated correspondence: every terminating reference
  outcome is matched by a generated outcome.
- Generated-to-reference realization: every terminating generated outcome
  is matched by a reference execution with some sufficient fuel.

Outcomes include related success values, the relevant failure kinds, and
observable state changes. The current stateful boundary requires exact
final-counter equality, including on failures. Each example must declare
its input representation, configuration, extern contracts, and observations;
printing or packet output needs a suitable observation contract if included.
The supported domain cannot silently exclude behavior the claim concerns:
for a type checker, rejecting ill-typed but representable programs matters.

This target does not require proving termination for every input. Exhaustion
at one reference fuel is not a semantic failure or evidence of divergence.
The reverse direction requires an actual finite execution witness, not just
determinism. Neither direction alone establishes both-way agreement.

The target concerns executable semantics. A generated logical relation may
be a sound overapproximation; `run_sound` then supports transferring universal
properties, but does not establish that each relational witness is executable.
Do not assume exactness or determinism of every generated relation.

There are three separate evidence boundaries:

| Question | Evidence |
|---|---|
| Are generated declarations and proofs valid Lean? | kernel checking and axiom audits |
| Does the generated executable implement the chosen AL meaning? | correspondence proofs with source identity, representation, dependency, and environment obligations |
| Does that Lean reference match upstream and intended P4? | manual port review and differential/conformance evidence; no end-to-end proof is claimed |

The completed field-update example establishes the second boundary in both
directions for its scalar source domain and transfers a consumer theorem.
The general generated certificates still establish only the forward
direction for the fragment in section 5.1.

Four rungs. We build rungs 1 to 3. Rung 4 is deliberately out of scope.

1. **Kernel checking.** Every generated declaration and theorem is
   kernel-checked. Build fails on any `sorry`, `partial`, or unproved
   termination. Warnings are errors. An audit checks the axioms of every
   generated theorem, so a native-decide escape or an imported axiom
   cannot pass silently.
2. **Differential testing.** Run the generated executable relations and
   upstream's interpreter on the same corpus; compare typing verdicts,
   IR, instantiation results, and output packets. Also run the Lean AL
   interpreter itself on the deep terms against upstream's (the second
   leg, `nano-p4-interp`, on the whole Nano-P4 corpus), which directly
   tests the semantics port. Ported builtins get generated
   unit-test obligations from upstream's test outputs. Mutation checks on
   both sides: mutate codegen and require rung 3 to fail; mutate the
   semantics port and require rung 2 to catch it.
3. **Proof-producing translation.** Requires the Lean formalization of
   the IL: a deep embedding of the IL AST plus an interpreter for it. For
   each definition `d`, codegen emits the shallow Lean definition `d`,
   the quoted IL term `⌜d⌝` (a structural copy of the JSON as Lean data),
   and a refinement theorem (section 5.1) discharged by a generic tactic.
   A failing tactic fails the build. Within the certified fragment, the
   proof checks the stated executable correspondence rather than trusting
   the emitter. Source identity and representation adequacy remain separate
   obligations. The two-way target above extends the current certificates.
4. **Verified translation function.** A universal theorem about the whole
   compiler is not planned. Per-artifact certification is the chosen
   approach; an unverified elaborator does not make alternatives impossible.

**What rung 3 buys, honestly.** It does not shrink the trusted base; it
moves it from the generator to the interpreter port. Sail's authors put
it plainly: their translation's semantics "is effectively defined by this
translation". What rung 3 gives instead is a trusted base that is
reviewable side by side with upstream (section 2.1) and cross-checked by
rung 2, in place of one that is neither. That is defence in depth. The
design measures both line counts and reports them.

### 5.1 The refinement theorem

This section describes the current one-way theorem, not the two-way target
above. The theorem is not `⟦⌜d⌝⟧ = d`. The interpreter works on generic IL
values and backtracks; the generated definition uses specific types and
models potentially partial computation. Every
precedent (CakeML's proof-producing translator, Cogent's certifying
compiler, certifying extraction for Coq) states a type-indexed
refinement relation and discharges it syntax-directedly. As built (M2,
`Refine/`, `Codegen/Validate.lean`, `Tactic/Refine.lean`):

- **The value relation** is one relation for every generated type:
  `Rel v x := canon v = canon (toValue x)`, where `canon` erases the
  notes and regions the interpreter never reads (and reduces the two
  payloads its comparison does not look inside). `eq_iff_canon` proves
  that the interpreter's `Value.eq` is exactly canonical equality, so
  `Rel` is the kernel of the interpreter's own equality. The certified
  fragment is first-order; full AL has higher-order features requiring
  additional contracts. Equality compatibility alone does not establish
  compatibility with every observation, such as hinted printing.
- **The statement**, per definition `X` with inputs `τ₁ … τₙ` (a
  relation's outputs `σ` as a tuple):

      theorem X.refines (fuel : Nat) (cfg : Config) (ctx : Ctx.t) (internal : Bool)
          (hguard : cfg.guard = false) (hfenv : ctx.local.fenv = [])
          (hspec : HoldsSpec Lib.spec ctx.global)
          (v₁ … vₙ : value) (p₁ : τ₁) … (pₙ : τₙ) (h₁ : Rel v₁ p₁) … :
          Refines (fun vs (o : σ) => Outs vs [toValue o])
            (invoke_rel fuel cfg internal ctx (Q.i "X") [v₁, …, vₙ])
            (ExceptT.mk (Lib.X.run p₁ … pₙ))

  `Refines P m n` says every defined result of the interpreter's `m` (a
  success or a failure; fuel exhaustion imposes no obligation) is matched
  by a defined result of the generated `n`: the
  same failure kind, or values related by `P`. So the theorem covers
  every fuel and every input, failures included, which is what makes a
  rule group's `else` and a `does not hold` premise meaningful. A
  function's statement relates the results by `Rel` directly.
  `HoldsSpec Lib.spec g` says the global tables hold every quoted
  definition (`Lib.spec` is the list of all `d.al`, as `Ctx.init` would
  load them); the guard is off because the interpreter's dynamic type
  checks are instrumentation, not meaning; the local function table is
  empty because no definition in the fragment takes a function argument.
- **Recursion.** A recursion group gets `X.refines_group : ∀ fuel,
  stmt_X fuel ∧ …` by strong induction on the fuel, and a corollary per
  member; a call inside the group uses the induction hypothesis at the
  callee's smaller fuel, a call outside it the callee's theorem. Nothing
  about `partial_fixpoint` is needed on this side: the generated
  definition is only called, never unfolded below its own body.
- **The tactic** `refine_al` is a lockstep symbolic execution. The
  interpreter side is computed by `simp` with the interpreter's own
  equation lemmas on the concrete quoted syntax, one fuel level at a time
  (`cases` on the fuel at the head of the chain; the zero case is
  divergence); the generated side is walked by the rules of
  `Refine/Calc.lean`: a `have` binds, a call is paired with the
  interpreter's invocation through the callee's theorem, a `match` or
  `if` on a variable is split by `cases`, sequential choice alternative
  by alternative, and at a `pure` the results are related by computing
  `canon` on both sides. When the interpreter inspects a value whose
  generated counterpart is a variable, that variable is split, which is
  the case analysis the generated code performs too; the shape of the
  interpreter's value then follows from the fact by a dozen inversion
  lemmas. There is no per-construct lemma about the interpreter: the
  interpreter's definitions are the lemmas, which is what makes the
  library small and the port the only trusted text.
- **The fragment.** `Codegen/Validate.unsupported` decides syntactically
  which definitions get a theorem, closed under callees; the rest are
  listed in the generated module with their reasons. Whatever the tactic
  cannot close fails the build; nothing is `sorry`ed. At M2 the fragment
  holds 18 of Nano-P4's 153 definitions, all functions: every relation
  calls a builtin or iterates, so the relation form of the statement is
  exercised only in development, not in the build, until the
  fragment grows (M3).
- **What it does not cover.** The theorem quantifies over generated
  values and their `toValue` images, so the generated *types* and their
  `ToValue` instances are part of the statement, not checked by it: a
  dropped variant case or a misplaced field is invisible to rung 3 and is
  caught only by rung 2 (the decoder round trip on the corpus). The
  table hypothesis `HoldsSpec` has its witness (`holdsSpec_of_init`: the
  tables `Ctx.init` builds from the quoted spec satisfy it, so a run of
  the interpreter on `NanoP4Spec.spec` is an instance); the quoting
  `d.al` is checked against the decoded export by `check-quotes` on every
  gate invocation: all 342 quoted Nano-P4 definitions, in order, with
  regions and hints erased and source `VarD` entries omitted as `Ctx.init`
  does. The comparison uses independently derived AST equality, not the
  quoting emitter. This is a runtime check, not a kernel proof of quoting
  correctness; full-P4 quotations will be checked when that library builds.
- **Diagnosing a failing proof.** Build the one group:
  `lake build NanoP4Spec.Refinement.<group>` (the module is named after
  the group's first definition, with `'` spelled `_p`). Add
  `set_option refine_al.trace true in` before the theorem in a scratch
  copy of that module and run `lake env lean` on it: the tactic prints
  each step (fuel split, callee, case split, the condition it splits on)
  and at the end the time per phase, to stderr; a failure names the
  interpreter step and the generated term it was paired with, and the
  last action. The usual causes are a missing unfolding lemma in the simp
  set (the interpreter term stays stuck) or a construct outside the
  fragment the syntactic check missed.
- **Failure vs divergence.** `partial_fixpoint` rejects backtracking
  written with `<|>` because it is not monotone in the flat order. The
  interpreter therefore separates failure as data from divergence,
  returning `Option (Except Fail v)` or the equivalent transformer, and
  this was decided before the port, not after. General reverse realization
  is not generated. The handwritten field-update proof supplies this
  direction for its bounded domain (sections 1.1 and 5).

The experimental stateful calculus (`Refine/StateCalc.lean`) strengthens
the result relation with exact final-counter equality for every terminating
outcome, including mismatch and hard error. Its bind, choice, negation
and ordered-iteration rules are kernel-proved. An interpreter-only step
may be skipped only when its terminating executions succeed and preserve
state. Divergence remains unconstrained by one-way partial correctness.
`RejectedPrefix` records the states consumed by earlier mismatching
alternatives; a recursive structural-rule fixture checks this approach
with `partial_fixpoint`. This is a calculus and proof fixture, not yet a
stateful AL-interpreter refinement theorem or generated full-P4 coverage.
Further bounded fixtures handle recursive calls inside rejected attempts
and ordered structural recursive premises. Stronger partial-correctness
motives carry exact all-outcome realization alongside successful structural
soundness. Iteration retains a structural premise per element with linked
states, not just executable equations; the kernel requires enclosing values
to be explicit inputs rather than captured nested-inductive parameters.

One effect-parameterized AL evaluator now supports both the existing pure
`Eval` interface and explicit-state `StateEval`. Stateful function and
relation entry points require an initial counter and return its final value
on success or either failure kind. Table initialization does not reset a
session; callers decide when to reset or continue it. Fresh allocation,
backtracking, negation, extern callbacks and tracing use this same carrier.
The existing pure Nano refinement statements remain unchanged. This shared
interpreter does not by itself provide stateful generated code or refinement
proofs, or establish guarded higher-order full-P4 execution.

The state oracle records 15 pinned upstream observations: ten complete
AL/session cases and five direct fresh-builtin cases. Complete AL runs in
sequential, cache-free, guard-disabled mode. It compares payloads and exact
post-state; upstream's public entry points collapse internal hard errors
and mismatches, so only the direct primitive cases compare failure tags
exactly. Signed wrap and invalid arity are primitive observations, not
complete-AL coverage. The fixture is checked on every gate and can be
regenerated from the pinned upstream interpreter.

### 5.2 Trusted vs checked

| Component | Status | Why | Does not establish |
|---|---|---|---|
| Lean 4 kernel | trusted | standard | |
| Upstream parser, elaborator and IL-to-AL algorithmization (OCaml) | trusted | produces the AL input; shared with the upstream P4 specification toolchain | that the spec is P4, or a proof that algorithmization preserves IL semantics |
| JSON dump of the IL | trusted | tiny and structural; round-trip tested against upstream's IL printer | |
| `P4SpecTec.Interp_al` (the AL interpreter in Lean, with `Runtime.Value.Match`, `Runtime.Type.*`, `Runtime.Dynamic*`, `Builtin.Call`) | trusted | the spec of the compiler; mirrors upstream's `interp/interp-al/` file by file and function by function; cross-checked by the second leg of rung 2 (`nano-p4-interp`: the port on the deep terms of the corpus against the AL export, 78 of 78 verdicts and 48 of 48 outputs agree) | agreement with SL or PL interpreters |
| `P4SpecTec.Runtime.Value.Value`, `Interface.P4.Unparse` | trusted | ports of value comparison and the note-aware printer, file by file; 12 printer fixtures compared with pinned upstream observations on every gate | hinted-print refinement or arbitrary external-value note provenance |
| `P4SpecTec.Interface.Builtin` | trusted | ports of upstream builtins, one file per file, at the OCaml file's path; unit tests in `P4SpecTecTest/Builtins.lean` (generated obligations from upstream outputs are planned) | |
| Dynamic Nano target/driver ports under `P4SpecTec.BackendSim` | trusted within the documented bounded profile | pinned direct and captured-input packet/driver observations; shared verify preserves upstream's ABI and the actual Nano incompatibility | complete generated typed target, Lean boot/STF support, all packet behavior, or fidelity to a real device |
| `P4SpecTec.Codegen` | checked within the supported fragment | 18 Nano-P4 definitions validated by rung 3; all Nano-P4 quotations compared with the export | correctness of definitions outside the refinement fragment |
| Generated `NanoP4Spec`; planned `P4Spec` | checked to the recorded coverage | Nano-P4 is kernel-checked and differential-tested, with refinement for 18 definitions; full-P4 generation is still blocked | full-P4 correctness before M3's remaining phases |
| Lean elaborator and compiler | checked / trusted | the kernel checks elaboration; the compiler is trusted for `#eval` and differential runs only | |

### 5.3 Deviations forced by Lean

The only places the Lean side does not mirror upstream. Each entry names
what changed, why Lean needs it, and where it lives. Anything not listed
here is a bug.

| Deviation | Why Lean needs it | Where |
|---|---|---|
| Recursive groups defined by `partial_fixpoint` in `Eval := ExceptT Fail Option`, definitions typed `Option (Except Fail T)` with `ExceptT.run`/`ExceptT.mk` around bodies and calls; pure variable bindings are `have`, not `let` | Lean requires a termination argument or a monotone fixpoint; the spec's recursion is not always structural; `partial_correctness` is derived only for `Option`-typed definitions; the monotonicity tactic cannot eliminate a match on a `let`-bound variable | `Prelude/Eval.lean`, `Codegen/Funcs.lean`, `Codegen/Rels.lean`, `Codegen/Fmt.lean` |
| A recursive group spanning spec files is emitted in the last file's module | a `mutual` block cannot cross files | `Codegen/Emit.lean` |
| Type aliases are unfolded in the constructor arguments of a recursive group | the kernel's nested-inductive check does not see through an `abbrev` | `Codegen/Types.lean` |
| Every reference to a generated name is qualified with the library name; type parameters are `τX` | spec variables are named after their types and would shadow them | `Codegen/Names.lean` |
| Equality on generated types is equality of their IL values | `deriving BEq` on nested inductives is opaque; value equality is upstream's `Value.eq` | `Codegen/Types.lean`, `Prelude/Value.lean` |
| In the IL mirror, `iterexp`, `iterprem` and `typorigin'` are named inductives, EL hints are raw JSON, `Bigint.t` is `Nat`/`Int`, the polymorphic-variant unions are flat inductives | the kernel rejects a pair holding a list of a type being declared; the EL is not mirrored; Lean has no bigint or open unions | `IL/Ast.lean` |
| Failures upstream reports as OCaml exceptions or `assert false` (division and modulus by zero, `^`, a failed downcast, a pattern shape that does not match, an optionality mismatch) are `Fail.err` in the executable encoding, the kind upstream never backtracks over | Lean has no exceptions; none of these is reachable on the guarded AL, and `err` is the nearest kind | `Codegen/Exp.lean`, `Prelude/Num.lean`, `Prelude/Eval.lean` |
| Each relation emitted twice, `Prop` and executable | a `Prop` cannot be run; an executable function cannot be reasoned about by rule induction | `Codegen/Rels.lean`, `Codegen/Props.lean` |
| In the `Prop` encoding an iterated premise is `∀ elems collected, (elems, collected) ∈ List.zip lists tmp → …` with the length equation beside it; its relation-free facts sit under `∃` for their temporaries, each relation fact is an implication from those facts, and the ∀-bound names are the spec's | the kernel rejects a relation under `∃`, `∧` or `∨` inside its own constructors ("nested inductive datatypes parameters cannot contain local variables") and accepts it under `∀` and `→` | `Codegen/Props.lean` |
| A `does not hold` premise is `R'.run args = some (.error Fail.unmatch)` in the `Prop` encoding; an `else` group carries no negation of the other groups | a relation cannot occur negatively in its own definition; the executable encoding orders the `else` group last and keeps the meaning | `Codegen/Props.lean` |
| A temporary the spec does not name (the collected list of an iteration, a hoisted call whose result is matched by a pattern) is a constructor argument named `tmp_n` | the AL has no name for it | `Codegen/Props.lean` |
| `BEq` instances, not `DecidableEq`, on nested inductives | `DecidableEq` deriving fails on nested inductives (lean4#2329) | `Codegen/Types.lean` |
| Numerics as `Nat`, `Int` and `Rat` with explicit conversions | Lean has no unified number type; collapsing to `Nat`, as the Wasm Lean branch does, is wrong | `Prelude/Num.lean` |
| Semantic text uses `ByteText`, a `ByteArray` wrapper, throughout IL values, generated types and the interpreter; identifiers and atoms remain `String` | upstream text is an arbitrary byte sequence, while Lean `String` requires valid UTF-8; byte updates can invalidate an initially valid string. UTF-8 conversion is explicit and decoding is checked | `Util/ByteText.lean`, `Lang/Il/Ast.lean`, `Codegen/Types.lean` |
| JSON ingress rejects invalid UTF-8 and unpaired surrogate escapes, including cases a parser would silently replace | JSON's Unicode strings are not a general arbitrary-byte transport. This is a fail-closed input restriction, not a lossless encoding of every OCaml string | `Util/Yojson.lean` |
| Checked text-builtin dispatch preserves arity mismatches as `Fail.unmatch` and maps assertions/invalid integer parsing to `Fail.err`; other builtin families retain the legacy failure classification | upstream catches `BuiltinError` for backtracking but does not catch these hard exceptions. Typed generated wrappers admit only well-typed, correctly applied arguments | `Interface/Builtin/Call.lean`, `Codegen/Funcs.lean` |
| Structural equality for values | the OCaml unique-id scheme is a performance device tied to a mutable allocator | `Runtime/Value/Value.lean` |
| Generated variant values carry static type notes when converted back to IL values; printing is admitted only when constructor origins and subtype bridges preserve the selected hint policy | the typed representation omits runtime note provenance; a checked compatibility condition avoids adding otherwise unused metadata | `Codegen/PrintHints.lean`, `Codegen/Types.lean` |
| `Alter.OtherH` retains raw EL JSON; unsupported print expressions fail generation, and invalid placeholders or unprintable values return errors | EL is not otherwise embedded and Lean has no OCaml exceptions; all 190 hints at the pin use the six supported alternation forms | `Lang/Hints/Alter.lean`, `Lang/Hints/AlterJson.lean`, `Interface/P4/Unparse.lean` |
| One effect-parameterized interpreter specializes to `Eval` or `StateEval`; every function of its recursive block takes fuel, one unit per call; `none` is exhaustion | the recursion is not structural; fuel preserves the port's shape and supports induction on evaluation. A shared evaluator avoids duplicating the trusted control flow when adding state | `Interp/Effects.lean`, `Interp/InterpAl/Interp.lean` |
| No mutable context, caching, hooks, backtraces, deterministic mode; the global tables are immutable hash maps, the local environments association lists; the extern implementations and the guard flag are a `Config` parameter | pure functions, with a sequential-mode comparison boundary; deterministic checking can consume extra fresh identifiers, so stateful comparisons must use upstream `det=false` | `Interp/InterpAl/` |
| Pure context/runtime helpers retain `Eval` and are lifted into the evaluator's carrier; failure traces are dropped; interpreter `debug` premises evaluate but do not print their expressions; exceptions and failed assertions become `Fail.err` | pure helpers need no state; Lean uses explicit error data. Stateful tracing observes the actual result once without resetting or rerunning it | `Interp/InterpAl/Backtrack.lean`, `Interp/Effects.lean`, `Interp/InterpAl/Interp.lean` |
| Legacy total `Value.Match`/`Type.Subst` APIs retain false/identity fuel fallbacks, deterministic function binder names and the old higher-order substitution behavior; the interpreter uses additive checked APIs with explicit exhaustion and hard errors instead | retain existing proof-facing APIs while migrating execution; the checked path must not confuse exhausted recursion with a mismatch or successful substitution | `Runtime/Value/Match.lean`, `Runtime/Type/Subst.lean`, `Interp/InterpAl/Interp.lean` |
| Checked type expansion, equivalence and nested parameter conversion use bounded fuel; nonempty substitution through `FuncT` is explicitly unsupported until upstream's separate `Type.Fresh` state is modeled | these recursions are not structurally bounded by input values; inventing deterministic names can change returned types, so unsupported allocation is an error rather than fabricated data | `Runtime/Type/Expand.lean`, `Runtime/Type/Equiv.lean`, `Runtime/Type/Typ.lean`, `Runtime/DynamicAl/Func.lean` |
| Function equivalence pairs binders with private NUL-prefixed markers before alias expansion; it does not allocate or expose upstream `Type.Fresh` names or advance that separate counter; mixfix comparison omits OCaml's physical-identity shortcut | a result-only Boolean comparison needs alpha-renaming, not observable names; the current boundary is well-formed parsed identifiers and bounded signatures, not future substitution after consumed type-fresh allocations or malformed identity-sharing inputs | `Runtime/Type/Equiv.lean` |
| The builtin dispatcher works on values through typed ports; stateful interpreter dispatch additionally implements `fresh_typeId` after zero-arity validation, but omits `add` registration | one port per builtin file; registration is used by upstream's omitted caches. The pure specialization still has no fresh allocation | `Interface/Builtin/Call.lean`, `Interp/Effects.lean` |
| Fresh IDs use explicit `ExceptT Fail (StateT (BitVec 63) Option)` state, retaining allocations on failure and negation; integrated into the interpreter, not yet codegen | pure Lean has no global mutable counter; signed 63-bit wrapping matches OCaml `int` on the pinned 64-bit platforms, not 32-bit hosts; callers explicitly choose session/reset boundaries | `Prelude/StateEval.lean`, `Interp/Effects.lean` |
| A hyphenated upstream directory is a camel-cased Lean directory (`interp-al` is `InterpAl`) | a hyphen cannot be in a module name | `scripts/check-mirror.py` |
| `is_iter_var_exp` recurses on the size of the expression (`termination_by`) rather than structurally | it descends through the phrase's payload, which structural recursion does not see; a fuel here would make a low-fuel run take the general iteration path instead of diverging, which rung 3 cannot allow | `Interp/InterpAl/Interp.lean` |
| The refinement theorems are in generated modules after the spec files: `Refinement/Spec` (the quoted spec as a list), one module per recursion group importing its callees' groups, and `Refinement` gathering them with the coverage; one `HoldsSpec` hypothesis over the whole spec | the theorems need every quoted definition (a callee's theorem needs its own callees' table entries), and one hypothesis over the whole spec avoids listing the transitive callees of every definition; a module per group lets Lake recheck only the groups an edit touches, and independent groups in parallel; only these modules import the refinement calculus and tactic, so editing the tactic leaves the spec modules built | `Codegen/Emit.lean`, `Codegen/Validate.lean` |
| The `Q.*` quoting constructors and `mkPhrase` are reducible | the driver's `simp` must see through them definitionally: a rewrite under `decide` with a non-reducible definition leaves an ill-typed term | `Refine/Quote.lean`, `Util/Source.lean` |
| `ToValue (α × β)` flattens a right-nested product into one IL tuple | the generator renders a spec tuple type as a right-nested product and its value as one flat tuple; a spec tuple nested inside a tuple (none in Nano-P4) would need a wrapper type (M3 trigger) | `Prelude/Value.lean` |
| Mutual block grouping by dependency | Lean requires mutually recursive definitions in one `mutual` block | `Codegen/Funcs.lean` |

### 5.4 Per-construct encodings

Codegen performs no IL-to-IL passes; these are the local encodings it
applies instead, each documented in the module that implements it.

| IL construct | Lean encoding |
|---|---|
| Subtype pair `S ⊆ T` (from `e <: T`, `e as T`) | three generated functions per instantiated pair, by matching cases with equal mixops: `S.to_T : S → T`, `T.of_S : T → Option S`, `T.is_S : T → Bool`. Parameterized pairs retain both applications and use deterministic structural specialization names below those namespaces; monomorphic names are unchanged. Both variants are instantiated before comparing alias-equivalent payload types, as upstream's variant subtype relation requires. Missing cases, malformed applications, free type parameters and unequal payloads fail generation; no covariant payload conversion is inferred. Numeric `nat ⊆ int` uses `Int.ofNat`, `Num.toNat?`, `0 ≤ i`; tuples and iterators are pointwise. The AL's `subcheck` is not consulted and `RecurseSC` argument checks are not generated. |
| Rule group with `else` group; clauses with `else` | alternatives in order (`<|>` in `Option`), the `else` last, as the AL interpreter's sequential mode |
| Mixfix notation | constructor names from the atoms (`Names.ctorName`); struct fields from their atoms |
| Iterators `?`, `*` with dimensions | `Option`, `List`; joint iteration zips the bound lists and maps, binding variables unzipped; an iterated premise likewise, with `mapM` |
| Path update `e[p = v]` | `{ e with a.b := v }` for dotted paths; root-index list replacement uses `Iter.setIdx`, text replacement uses `ByteText.setIdx`. Both evaluate base/replacement/index in that order and give `Fail.err` out of bounds; text replacement requires exactly one byte and preserves invalid-UTF-8 results. Sliced updates and nested index prefixes remain rejected. |
| Partial functions, downcasts, indexing, slicing, calls | hoisted into `let x ←` statements of the enclosing `do` block (A-normal form), `none` on failure, never a default value (the Wasm Rocq backend's defaults produced provably false lemmas) |
| Extern syntax, `extern dec`, `extern relation` | `ExternValue`; fields of the generated class `Externs` |
| Tables (`table dec`) | a function by cases over the rows |
| Builtins (`builtin dec`) | a wrapper around the port of the same OCaml file under `Interface/Builtin/`; sets and maps unwrapped to element lists. `print_` uses a literal per-spec table keyed by type and mixop, with cursor, fusion and empty-piece semantics ported from upstream. Placeholder bounds, supported forms, constructor-note provenance and policy compatibility across inherited cases/casts are checked before generation. Interpreter callers initialize `Config.withPrintHints` from the same AL spec. Printer errors become `Fail.err`, not retryable mismatches. |
| Values of generated types | `ToValue` (structural) and `OfValue fuel` (decoder) instances per type, for programs, printing and equality |
| Relation, `Prop` encoding | `inductive R : args → Prop`, one constructor per rule path named by `Names.ruleName` (`rule<k>` when the spec names neither group nor rule), implicit arguments for the path's variables with the types the AL notes give, hypotheses in statement order; `R.run_sound` per relation, `<first>.run_sound_group` per recursive group, `#audit_axioms` after each |

Hint-policy compatibility checks justify the generated representation's
specific static note changes, not arbitrary note changes in decoded input.
The existing `Rel` erases notes, and quoted AL drops hints; neither it nor
`HoldsSpec` alone establishes a hinted-print correspondence theorem. Print
builtins remain outside the refinement fragment until an appropriate
policy/environment contract is proved. The printer's twelve recorded
upstream observations cover cursor ordering, fusion, empty spacing,
type-specific lookup, nested hints, unused unprintable arguments, byte
escaping and ASCII-only case conversion; they are differential tests,
not refinement proofs.

Text length, indexing, slicing, concatenation, comparison and replacement
operate on bytes, not Unicode characters. Generated text literals use
explicit UTF-8 encoding when valid, and byte arrays otherwise; quoted AL
uses the same lossless representation. The text-builtin oracle records
hexadecimal payloads and exact upstream exception classes, checking the
dispatcher, interpreter and production-emitted wrappers. These observations
are regression evidence, not a proof of complete builtin correspondence.
Existing but malformed expected-output files fail the differential harness;
they cannot silently disable output comparison.

### 5.5 Test sources (all from upstream)

- p4c sample corpus: hand-written, mostly well-typed programs. Main source
  for typing and instantiation comparison; seed set for the fuzzer.
  Upstream's `excludes/` lists say which programs to skip and why.
- Negative-test fuzzer (`p4spectec testgen`, `fuzzer/`): mutation-based
  generator of *ill-typed* programs, guided by spec coverage. Exercises
  the failure paths of the typing relation, where a first-match
  executable encoding and a backtracking interpreter are most likely to
  disagree.
- STF packet tests (`testdata/p4testgen/`): program + input packets +
  expected outputs. Used by the packet simulation comparison.

There is no random well-typed program generator. Options if wanted later:
p4c's p4smith, or enumerating derivations of the generated inductive typing
relation. Not planned for the start.

## 6. Code organization

The tree at the end of M2 (M3 and M4 entries are planned):

One Lake package `p4spectec` with several libraries. The core library and
root namespace are `P4SpecTec`, aligned with upstream. `SpecTec` alone
refers to the Wasm-DSL project and is not used as a name here.

```
p4-spectec-lean/
├── AGENTS.md                     # entry point for people and agents; reading order (no CLAUDE.md)
├── README.md
├── flake.nix, flake.lock         # the development environment; every command runs inside it
├── lean-toolchain
├── lakefile.toml                 # libs: P4SpecTec, P4SpecTecTest, P4Lib, NanoP4Spec, P4Spec; exe: p4spectec-gen
├── docs/                         # describes the artifact; never links into .agents/
│   └── design.md                 # this file
├── .agents/                      # describes the work; the resumable state
│   ├── status.md, decisions.md, roadmap.md, notes/, reviews/
│
├── upstream/
│   ├── p4-spectec/               # git submodule, pinned (the gsoc-nano-spec branch)
│   ├── nano-p4-spec/             # git submodule, pinned: the Nano-P4 spec files
│   └── patches/
│       └── 0001-json-export.patch   # `elab -json`, `algo -json`, `nano parse -json`
│
├── exports/                      # committed JSON: the OCaml → Lean handoff
│   ├── nano-p4.al.json.gz        # both specs: .json.gz + .json.sha256; extracted JSON ignored
│   └── programs/nano-p4/         # booted programs with upstream's verdicts
│
├── P4SpecTec/                    # core library, language-agnostic
│   │                             # a mirrored module sits at its OCaml file's path, capitalised
│   ├── Util/Source.lean          # mirrors util/source.ml; Util/Yojson.lean is ours (decoding helpers)
│   ├── Lang/Xl/, Lang/Il/, Lang/Al/   # mirror lang/xl/, lang/il/ast.ml, lang/al/ast.ml; Json.lean beside each is ours
│   ├── Domain/Atom.lean, Domain/Mixfix.lean   # mirror domain/
│   ├── Runtime/Value/Value.lean  # TRUSTED: mirrors runtime/value/value.ml (Make, Get, compare, eq)
│   ├── Runtime/Value/Match.lean  # TRUSTED: mirrors runtime/value/match.ml (subtyping of values)
│   ├── Runtime/Type/             # TRUSTED: mirrors runtime/type/{typdef,typ,subst}.ml
│   ├── Runtime/Dynamic/Var.lean, Runtime/DynamicAl/{Rel,Func}.lean   # TRUSTED: the environments' keys and entries
│   ├── Interface/P4/Unparse.lean # TRUSTED: mirrors interface/p4/unparse.ml (the printer)
│   ├── Interface/Builtin/        # TRUSTED: mirrors interface/builtin/ file by file; Call.lean is the dispatcher on values
│   ├── Lang/Hints/Input.lean     # mirrors lang/hints/input.ml (input positions, split and combine)
│   ├── Interp/InterpAl/          # TRUSTED: mirrors interp/interp-al/{backtrack,ctx,interp}.ml (M2)
│   ├── Prelude/                  # ours: the runtime aggregate the generated code imports
│   │   ├── Value.lean            # ToValue, OfValue, equality through values
│   │   ├── Eval.lean             # the Eval monad: Fail, orElse, monotonicity, run lemmas (M2)
│   │   ├── Extern.lean, Num.lean, Iter.lean
│   ├── Refine/                   # ours: rung 3 (M2)
│   │   ├── Value.lean            # canon, Rel: IL values against generated values, up to notes
│   │   ├── Quote.lean            # Q.*: the smart constructors the quoted definitions are built with
│   │   └── Calc.lean             # Refines, its rules, Holds/HoldsSpec, exposure lemmas
│   ├── Codegen/                  # NOT trusted: validated per definition (M2)
│   │   ├── Names.lean            # the naming rule; Keywords.lean is generated from Lean's token table
│   │   ├── Env.lean, Graph.lean, Fmt.lean   # spec environment; SCCs; the printer
│   │   ├── Types.lean            # TypD → inductive / structure / abbrev, ToValue/OfValue, subtype bridges
│   │   ├── Exp.lean              # expressions, patterns, premises in A-normal form
│   │   ├── Funcs.lean            # FuncDecD, BuiltinDecD, TableDecD → def; the Externs class
│   │   ├── Rels.lean             # RelD → run function
│   │   ├── Props.lean            # RelD → Prop inductive, run-soundness theorems, audits (M2)
│   │   ├── Reify.lean            # every definition quoted as Lean data, `d.al` (M2)
│   │   ├── Validate.lean         # the refinement theorems and the fragment they cover (M2)
│   │   ├── Emit.lean             # the plan: groups, module assignment, module text
│   │   └── Main.lean             # `lake exe p4spectec-gen <export> --lib <Lib> [--update|--check]`
│   ├── Tactic/                   # the proof side (M2)
│   │   ├── RunSound.lean         # run_sound, run_sound_group: symbolic execution against the Prop
│   │   ├── Refine.lean           # refine_al: lockstep execution of the interpreter and the generated code
│   │   └── Audit.lean            # #audit_axioms
├── P4SpecTecTest/                # test-only: decode test, the differential runners (Diff/NanoP4Run/, Diff/NanoP4Interp/)
│
├── NanoP4Spec/                   # GENERATED, committed, diffed in CI; one module per Nano-P4 spec file, named as it,
│                                 # then Refinement/: the quoted spec as a list (Spec) and the rung 3
│                                 # theorems, one module per recursion group; Refinement.lean gathers them
├── P4Spec/                       # GENERATED at M3; Targets/ hand-written, mirrors backend-sim/<target>/
│
├── P4Lib/                        # M4; independent of the generated spec
│
├── docs/timing-nano-p4.md        # per-module elaboration times
├── test/diff/run.py              # rung 2 harness, typing leg
└── scripts/                      # check.sh (the gate), check-mirror.py, gen-keywords.sh, build-upstream.sh,
                                  # export-spec.sh, export-program.sh, time-elab.sh
```

Choices embedded in the tree:

- Submodule plus patch, not a fork. Bumping upstream is one line.
- JSON exports are committed as the OCaml/Lean contract; Lean builds need
  no OCaml. Both spec snapshots use deterministic gzip and
  a raw checksum; the gate verifies and extracts it. Its readable census
  stays in Git, but ordinary text diffs of the compressed AST are lost.
  CI checks generated Lean and the census against these snapshots; it
  does not re-export upstream specifications on every run.
  Tracked files are capped at 5 MiB by the gate; larger or high-churn
  inputs should use checksum-pinned external artifacts. History is not
  rewritten merely to migrate existing snapshots to compressed storage.
- Generated Lean is committed and is the build input. CI regenerates from
  the exports and fails on any diff. Generated files carry a grep-able
  header naming the generator and the spec file, and are never
  hand-edited: the Wasm Rocq team re-patches its generated file after
  every regeneration, which is the failure mode to avoid.
- Trusted files are marked and each mirrors an upstream file.
- `P4Lib` does not depend on `P4Spec`. Target instances do, so they live
  next to the spec.
- Lake layout: importable modules under the root, test-only modules under
  a `Test` root, no Mathlib, one toolchain pin.

Rung 3 lives in: `Interp/InterpAl/` and the runtime it needs (reference
side, trusted), `Refine/` (the value relation, the quoting constructors
and the refinement calculus), `Codegen/Reify.lean` and
`Codegen/Validate.lean` (generation side), `Tactic/Refine.lean` (proof
side, where the real work is), and `NanoP4Spec/Refinement/` (the
generated theorems).

### P4Lib

Serves users of the generated semantics, not generation itself.

- `Packet.lean`: byte sequences, header extraction and emission.
- `BitVec.lean`: the spec defines `bit<n>` arithmetic as unbounded-integer
  arithmetic modulo 2^n, so generated code computes with `Int`. That is
  correct but hostile to proof automation, which works on core `BitVec`.
  The bridge is a lemma library equating the two under the obvious
  conversion so goals can be handed to `bv_decide`. Needed by no rung;
  only by downstream proofs. Built last, driven by the first real proof.

## 7. Scale

The full spec is 1,090 rules and 561 functions, and each relation
produces a `Prop` inductive, a run function, a reified term, theorems and
lemmas. Prior art says elaboration cost is the risk that surfaces last
and hurts most: Isabelle's SpecTec backend needed passes to cap
constructor counts because datatype compilation is quadratic; Sail's
RISC-V output is 175k lines of Lean; Islaris could not manipulate the
Armv8 model in Coq at all. So:

- Per-file modules (section 4.1), so Lake parallelizes and a change to
  typing does not rebuild instantiation.
- Per-file elaboration timing from the first Nano-P4 output, in M1, with
  a tracked table, so encoding choices are made while they are cheap to
  change.
- Generated types derive only what is used; no `DecidableEq` on wide
  variants.
- Proof-checking time of generated theorems measured from M2 and
  budgeted like build time.

## 8. Engineering conventions

- **`AGENTS.md` is the single entry point.** No `CLAUDE.md`.
- **`docs/` describes the artifact, `.agents/` describes the work.**
- **`.agents/status.md` holds current truth only;** updated at every
  checkpoint.
- **`.agents/decisions.md` is a register, not a diary.**
- **Compaction at milestone boundaries;** git history is the archive; no
  tags.
- **Checkpoint unfinished work explicitly.** Commit validated changes;
  isolate incomplete experiments on a feature branch with a clear WIP
  handoff. Every push requires the full local gate; blocked publication
  is recorded with the local commit and remaining obligations.
- **One environment, defined by Nix.** Every command, locally and in CI,
  runs inside `nix develop`. Lean comes from elan at the version
  `lean-toolchain` names; the OCaml side comes from nixpkgs' default
  package set, the one the binary cache carries. A personal `.envrc` is
  ignored.
- **Every external input is pinned and listed in one table:** P4-SpecTec
  by commit, nixpkgs by `flake.lock`, GitHub Actions by SHA, the Lean
  toolchain by version, Batteries by tag with the exact revision in the
  Lake manifest.
- **Warnings fail the build through `lake build --wfail`**, never through
  `warningAsError` in Lake options. A `sorry` is a warning and fails too.
- **Docstrings on every declaration; mirrored modules keep upstream
  names; our own code follows Lean style.**
- **Documentation and website.** Markdown in `docs/` and `.agents/`; a
  GitHub Pages site in three stages: none until M1; doc-gen4 API
  reference after M1; a Verso site with checked examples at M4.
- **No license header per file.**
- **Contribution workflow and PR-writing policy** live in `AGENTS.md`.
- **Independent read-only review after each step.**

## 9. Downstream use

p4blo (github.com/qobilidop/p4blo) is the motivating consumer: it wants
to prove its own architecture-free P4 IR semantics equivalent to
P4-SpecTec's, using this rendering. That downstream equivalence remains
its responsibility. This project's first consumer theorem validates a
complete source connection and guides the proof interface without making
the semantic core specific to p4blo. Consumers need:

- **A stable, versioned public surface.** Generated names, module split,
  the two relation encodings, and the per-relation lemma library already
  affect clients. Preserve the current naming contract; later changes are
  breaking. The final public proof API is open: proved wrappers or
  abstraction lemmas may be added based on the first consumer example.
- **Extra spec files as ordinary input** (section 4.1).
- **Externs as parameters** through one interface (section 4.1).

## 10. Milestones

**First consumer checkpoint, complete:** the field-update example in section
1.1 establishes two-way executable correspondence and transfers distinct-name
commutation on its scalar source domain. It brought the first downstream proof
forward from M4. This does not complete M3 or authorize broader expansion;
preserve paused M3 work and its unchanged gates.

- **M1, Nano-P4, rungs 1 and 2.** JSON dump patch, upstream built in the
  Nix shell, deep embedding, codegen for types, functions and relations
  with per-file text emission, prelude, mirror checks, per-file
  elaboration timing table, differential tests against upstream on the
  Nano-P4 corpus. Naming rule frozen at the end of M1.
- **M2, Nano-P4, rung 3 and the lemma library.** The `Prop` encoding of
  relations (carried over from M1), the fuel-free recursion strategy, IL
  semantics in Lean with the failure/divergence split, value relations
  per type, the per-construct lemma library and driver tactic,
  refinement and run-soundness theorems, per-relation inversion and
  determinism theorems, axiom audit, proof-checking time measured.
- **M3, full P4 1.2.5 spec.** Scale codegen and elaboration to ~80 files.
  Expect work on mutual blocks, `partial_fixpoint` monotonicity, and
  build times. Target instances arrive with the packet leg of rung 2.
  M3A exports the pinned full spec and measures the remaining obligations;
  generation now passes validated print hints and root-index list and byte
  text updates. Independent emission probes still identify stateful fresh
  identifiers as a barrier. M3B fixes
  thirteen subtype bridges by retaining their type
  arguments; all 567 bridge pairs now emit text. These probes are not
  evidence of a full-P4 build or proof coverage.
  The 108 source inputs become 80 top-level source-region files in AL;
  the final Lean module count is not yet known.
- **M4, P4Lib and the site.** BitVec bridge, packet types, broader
  downstream examples, Verso site. The first consumer proof is now the
  earlier acceptance checkpoint above.

## 11. Prior art consulted

Design: Wasm SpecTec's Rocq backend (branches `rocq-backend`,
`rocq-backend-proof`, `mech-backend`; IL2Coq thesis; PLDI 2024 paper) and
Lean backend (`lean4-wip`); CakeML's proof-producing translator (ICFP 2012,
JFP 2014); Cogent's certifying compiler (ICFP 2016, ASPLOS 2016);
certifying extraction (ITP 2019); Ott (JFP 2010); Lem (ICFP 2014); Sail
and its prover backends (POPL 2019, Morello ESOP 2022, CHERI-MIPS S&P 2020,
Islaris PLDI 2022); ESMeta/JISET/JEST; K's proof certificates (CAV 2021);
Petr4, P4Cub, Verifiable P4, HOL4P4; Lean's `partial_fixpoint`. Engineering:
cedar-spec, LNSym, Sail's Lean backend, Aeneas, Batteries, lean-mlir.

## 12. Open points

- Whether upstream's meta-circular spec matures enough to generate the IL
  semantics from it. Would turn the side-by-side review into a diff against
  upstream, but one hand-written semantics stays at the bottom of the
  stack regardless.
- Whether the full spec's generated modules stay reviewable as diffs; if
  not, review per section, never drop the diff check.
- How to extend generated-to-reference realization beyond the completed
  field-update domain. This direction is required by the agreed target;
  determinism alone does not supply the terminating reference witness.
- Which proof interface the consumer example needs: the existing logical
  relations, proved abstractions over AL-derived definitions, or eventually
  a different representation. No IL backend is scheduled now.
- Determinism at M2 (`Tactic/Det.lean`, `R.det : R i o → R i o' → o =
  o'`): attempted on relations with one rule path, no `else` group, no
  iterated premise, and callees that are themselves deterministic by
  theorem. That leaves 2 of 77 Nano-P4 relations (`Var_init`,
  `NanoSwitch_setup`): every other relation has several rule paths or
  reaches one through its callees (`Expr_ok` has 16). Several paths need
  a disjointness argument per pair of rules (their conclusions or
  premises cannot both hold), which is a real proof, not bookkeeping;
  upstream checks it dynamically in its deterministic mode. The finding
  is that determinism of the typing relation is a per-rule-pair
  obligation, and the tactic for it is M3 work if the goal is kept.
