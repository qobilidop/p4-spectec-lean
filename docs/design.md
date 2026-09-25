# p4-spectec-lean: design

Status: agreed design, 2026-09-24; revised 2026-09-25 after a prior-art
review (section 11) and again at the end of M1 for what building the
pilot taught (the AL as the export, fuel, module grouping, the naming
rule). "IL" below names the language; the export the compiler reads is
the AL, the IL after upstream's algo pass (section 3).
Diagrams: https://claude.ai/artifact/XCUhcd9cSsC4qBu2TjkiUJ (private).

## 1. Goal and thesis

A compiler from P4-SpecTec's IL (internal language) to Lean 4, written in
Lean, reusing the upstream OCaml frontend and elaborator unchanged, with
every generated definition validated by a machine-checked theorem. Plus a
small Lean library for P4 primitives that downstream verification projects
can import without the generated spec.

**Thesis.** Existing spec-DSL-to-prover backends (Ott, Lem, Sail, Wasm
SpecTec's Rocq and Lean backends) are unverified pretty-printers whose
output is only partly usable: Wasm SpecTec needed about fifteen IL-to-IL
passes before Rocq would accept its spec, and the generated Wasm 2.0 file
still has 64 axioms and 69 recursive functions turned into relations
because termination could not be shown; the Lean branch has 116 opaque
definitions and no proofs against it. P4-SpecTec's IL is different in
kind: elaboration already makes every rule algorithmic, with explicit
dataflow, no existentials, and side conditions for partial patterns. That
is most of the middlend Wasm had to build, done upstream, once. So:

> Because P4-SpecTec's IL is algorithmic, P4's mechanized semantics can be
> rendered into Lean as ordinary computable functions and rule-indexed
> inductive relations with nothing opaque, and that rendering can be
> validated definition by definition against a Lean formalization of the
> IL, in the manner of proof-producing translation.

**Claims.** Each has one experiment and one way to fail.

| Claim | Experiment | Fails if |
|---|---|---|
| 1. Complete rendering | every definition of the pinned spec renders and kernel-checks | any `opaque`, `axiom`, `sorry` or `partial` in generated code |
| 2. Agrees with upstream | the executable rendering answers the p4c corpus as upstream's interpreter does | an unexplained divergence |
| 3. Validated per definition | every generated definition carries a refinement theorem against the IL interpreter, proved by a generic tactic | a theorem the tactic cannot close |
| 4. Usable for proofs | a generated lemma library per relation, including a determinism theorem, that upstream only checks dynamically | a relation whose determinism cannot be stated or a downstream proof that needs hand-written adapters |

The project is self-contained. It depends on upstream P4-SpecTec and on
Lean, and on nothing else. It stays independent of upstream: upstream may
use it as a reference, but adoption is never a design criterion.
Downstream projects consume it; they do not shape it (section 9).

## 2. Principles

### 2.1 Correct by construction first, proofs second

Every place a reviewer can confirm correctness by inspection is a place
that needs no proof. So the design maximizes those places and spends
proof effort only on what is left. Concretely:

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
- Every relation carries an input hint. Elaboration guarantees all outputs
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
                                                     functions  def, structural or partial_fixpoint
                                                     relations  inductive R : Prop  +  def R.run : Option
                                                     ⌜d⌝, refinement theorems, lemma library
                                                     class P4Spec.Target  (externs and builtins)
                                                     ▲ imports P4SpecTec.Prelude
                                                     ▲ instantiated by P4Spec.Targets.*
```

Decisions:

- **Almost nothing in OCaml.** The JSON dump is a small patch to upstream.
  Everything else is Lean, including the compiler: the IL deep embedding
  must exist in Lean for validation anyway, so the generator and the
  validator share one AST and one decoder; Lean's own formatter gives
  canonical output and its token table gives correct keyword escaping;
  and a generator in Lean could one day be verified, one in OCaml never.
- **The compiler takes a list of spec files**, not a fixed directory, so a
  consumer can add an architecture or a contract written in SpecTec.
- **Text emission, one module per upstream spec file.** The generator
  prints `Std.Format` with its own printer at 100 columns and writes
  ordinary `.lean` files that Lake builds like any other module; keyword
  escaping uses Lean's own token table. A recursive group that spans
  files is emitted in the module of the last file (section 5.3). The files are
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
- **Externs and builtins become fields of a generated class.** Target
  instances are ports of upstream's OCaml target code. Every extern call
  in generated code goes through this one interface, so a free-monad
  outcome interface (what Sail needed for concurrency and symbolic
  execution) can replace it later without touching generated code.

### 4.2 Program flow

The spec files are the P4 *language* specification. A `.p4` file is a
value of the generated program type: data, not code. It needs a parser and
a decoder, not a second compiler.

```
prog.p4 + p4c/p4include → Preprocess → Parse → Boot (P4 AST → IL value) → --json
                                                                              │
                                                                              ▼
                                                        prog.json ──▶ decode : IL.Value → P4Spec.program
                                                                              │
                                                                              ▼
                                                        prog : P4Spec.program
                                                          #eval Program_ok.run ctx prog
                                                          theorem : Program_ok ctx prog ir
                                                          sim [Target := V1Model] prog pkt
```

- No P4 parser in Lean. The grammar is large, has a C-style preprocessor,
  and upstream's parser is the one the differential tests trust.
- Deep embedding first. A shallow embedding (P4 program → Lean functions)
  is a separate later compiler, proved correct against this semantics.
  Out of scope.

## 5. Verification and validation

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
   A failing tactic fails the build. Codegen is therefore not trusted.
4. **Verified translation function.** Not practical: Lean's own elaborator
   is unverified. Not planned.

**What rung 3 buys, honestly.** It does not shrink the trusted base; it
moves it from the generator to the interpreter port. Sail's authors put
it plainly: their translation's semantics "is effectively defined by this
translation". What rung 3 gives instead is a trusted base that is
reviewable side by side with upstream (section 2.1) and cross-checked by
rung 2, in place of one that is neither. That is defence in depth. The
design measures both line counts and reports them.

### 5.1 The refinement theorem

The theorem is not `⟦⌜d⌝⟧ = d`. The interpreter works on untyped IL
values and backtracks; the shallow definition is typed and total. Every
precedent (CakeML's proof-producing translator, Cogent's certifying
compiler, certifying extraction for Coq) states a type-indexed
refinement relation and discharges it syntax-directedly. So:

- Codegen generates, per IL type `τ`, a relation
  `R τ : IL.Value → ⟦τ⟧ → Prop` between IL values and values of the
  generated Lean type, mirroring CakeML's `INT`, `LIST_TYPE`, `PAIR_TYPE`.
  IL is first-order, so no function-typed invariants are needed, which
  removes the hardest part of CakeML's translator.
- For a function `f : τ₁ → … → τₙ → τ`:
  `Forall₂ R vs xs → interp ⌜f⌝ vs = some r → ∃ x, R τ r x ∧ f xs = some x`.
  Completeness, the other direction, is a second phase and is stated only
  where determinism is proved.
- For a relation, the same statement against the inductive `Prop`
  version, and separately `R.run i = some o → R i o` via
  `partial_correctness`; both share the value relation.
- The tactic is a fixed library: one lemma per IL expression and premise
  form (`interp_var`, `interp_call`, `interp_case`, `interp_iter`,
  `interp_prem_if`, …), per-type lemmas generated with each type, and a
  syntax-directed driver whose recursive case comes from the definition's
  own induction principle. Expect one generated induction step per
  (mutual) definition and zero manual lines. Nobody gets `rfl`; plan on
  rewriting from day one.
- **Effort and risk.** One-time library comparable to CakeML's core, a
  few weeks. Per definition, proof-checking time, not authoring, is the
  bottleneck; Cogent reports about twelve generated proof lines per
  source line. Measured from the first Nano-P4 output.
- **Failure vs divergence.** `partial_fixpoint` rejects backtracking
  written with `<|>` because it is not monotone in the flat order. The
  interpreter therefore separates failure as data from divergence,
  returning `Option (Except Fail v)` or the equivalent transformer, and
  this is decided before the port, not after.

### 5.2 Trusted vs checked

| Component | Status | Why | Does not establish |
|---|---|---|---|
| Lean 4 kernel | trusted | standard | |
| Upstream parser and elaborator (OCaml) | trusted | defines what the spec means; shared with the official P4 spec toolchain | that the spec is P4 |
| JSON dump of the IL | trusted | tiny and structural; round-trip tested against upstream's IL printer | |
| `P4SpecTec.Interp_al` (the AL interpreter in Lean, with `Runtime.Value.Match`, `Runtime.Type.*`, `Runtime.Dynamic*`, `Builtin.Call`) | trusted | the spec of the compiler; mirrors upstream's `interp/interp-al/` file by file and function by function; cross-checked by the second leg of rung 2 (`nano-p4-interp`: the port on the deep terms of the corpus against the AL export, 78 of 78 verdicts and 48 of 48 outputs agree) | agreement with SL or PL interpreters |
| `P4SpecTec.Runtime.Value.Value`, `Interface.P4.Unparse` | trusted | ports of value comparison and the default printer, file by file | hint-driven printing (rejected by codegen until supported) |
| `P4SpecTec.Interface.Builtin` | trusted | ports of upstream builtins, one file per file, at the OCaml file's path; unit tests in `P4SpecTecTest/Builtins.lean` (generated obligations from upstream outputs are planned) | |
| `P4Spec.Targets.*` | trusted | ports of upstream target code; tested by the packet leg of rung 2 | that any target is a real device |
| `P4SpecTec.Codegen` | checked | every output validated by rung 3 | |
| Generated `P4Spec` | checked | kernel-checked, differential-tested, validated per definition | |
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
| Structural equality for values | the OCaml unique-id scheme is a performance device tied to a mutable allocator | `Runtime/Value/Value.lean` |
| The interpreter runs in `Eval` too, and every function of its recursive block takes a fuel, one unit per call; `none` is exhaustion | the block's recursion is not structural (aliases unfold, rules call rules); a fuel keeps the port's shape the OCaml's and makes induction on the evaluation an induction on `Nat` for rung 3; `partial_fixpoint` over the whole block was the alternative and was not needed | `Interp/InterpAl/Interp.lean` |
| No mutable context, caching, hooks, backtraces, deterministic mode; the global tables are immutable hash maps, the local environments association lists; the extern implementations and the guard flag are a `Config` parameter | pure functions; these are instrumentation and checks, not meaning | `Interp/InterpAl/` |
| `'a backtrack` is `Eval`; failure traces are dropped; a `debug` premise prints nothing; upstream's exceptions and failed assertions are `Fail.err` | `Eval` is the one monad of the port and of the generated code; Lean has no exceptions | `Interp/InterpAl/Backtrack.lean`, `Interp.lean` |
| `Value.Match.sub_` and `Type.Subst` take a fuel; `Match.sub_`'s `FuncT` case (function values, through `Type.Equiv`) yields `false`; `Subst.freshen_tparams` derives fresh names from the parameter's name; a higher-order substitution substitutes the head | the recursion is not structural; Nano-P4 has no function values (an M3 item); no global counter | `Runtime/Value/Match.lean`, `Runtime/Type/Subst.lean` |
| The builtin dispatcher works on values through the typed ports; the `add` callback and `fresh_typeId` are not mirrored | one port per builtin file; the callback registers values for upstream's caches | `Interface/Builtin/Call.lean` |
| A hyphenated upstream directory is a camel-cased Lean directory (`interp-al` is `InterpAl`) | a hyphen cannot be in a module name | `scripts/check-mirror.py` |
| Mutual block grouping by dependency | Lean requires mutually recursive definitions in one `mutual` block | `Codegen/Funcs.lean` |

### 5.4 Per-construct encodings

Codegen performs no IL-to-IL passes; these are the local encodings it
applies instead, each documented in the module that implements it.

| IL construct | Lean encoding |
|---|---|
| Subtype pair `S ⊆ T` (from `e <: T`, `e as T`) | three generated functions per pair, by matching cases with equal mixops: `S.to_T : S → T`, `T.of_S : T → Option S`, `T.is_S : T → Bool`; numeric `nat ⊆ int` by `Int.ofNat`, `Num.toNat?`, `0 ≤ i`; tuples and iterators pointwise. The AL's `subcheck` is not consulted: a case's arguments are assumed to have the same types on both sides, which codegen asserts (the `RecurseSC` argument checks are not generated) |
| Rule group with `else` group; clauses with `else` | alternatives in order (`<|>` in `Option`), the `else` last, as the AL interpreter's sequential mode |
| Mixfix notation | constructor names from the atoms (`Names.ctorName`); struct fields from their atoms |
| Iterators `?`, `*` with dimensions | `Option`, `List`; joint iteration zips the bound lists and maps, binding variables unzipped; an iterated premise likewise, with `mapM` |
| Path update `e[p = v]` | `{ e with a.b := v }` for dotted paths; indexed paths are rejected until M3 |
| Partial functions, downcasts, indexing, slicing, calls | hoisted into `let x ←` statements of the enclosing `do` block (A-normal form), `none` on failure, never a default value (the Wasm Rocq backend's defaults produced provably false lemmas) |
| Extern syntax, `extern dec`, `extern relation` | `ExternValue`; fields of the generated class `Externs` |
| Tables (`table dec`) | a function by cases over the rows |
| Builtins (`builtin dec`) | a wrapper around the port of the same OCaml file under `Interface/Builtin/`; sets and maps unwrapped to element lists; `print_` uses the hint-free printer, and codegen rejects a spec with `print` hints |
| Values of generated types | `ToValue` (structural) and `OfValue fuel` (decoder) instances per type, for programs, printing and equality |
| Relation, `Prop` encoding | `inductive R : args → Prop`, one constructor per rule path named by `Names.ruleName` (`rule<k>` when the spec names neither group nor rule), implicit arguments for the path's variables with the types the AL notes give, hypotheses in statement order; `R.run_sound` per relation, `<first>.run_sound_group` per recursive group, `#audit_axioms` after each |

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

The tree at the end of M1 (M3 and M4 entries are planned):

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
│   ├── nano-p4.al.json           # (p4.al.json at M3)
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
│   ├── Codegen/                  # NOT trusted: validated per definition (M2)
│   │   ├── Names.lean            # the naming rule; Keywords.lean is generated from Lean's token table
│   │   ├── Env.lean, Graph.lean, Fmt.lean   # spec environment; SCCs; the printer
│   │   ├── Types.lean            # TypD → inductive / structure / abbrev, ToValue/OfValue, subtype bridges
│   │   ├── Exp.lean              # expressions, patterns, premises in A-normal form
│   │   ├── Funcs.lean            # FuncDecD, BuiltinDecD, TableDecD → def; the Externs class
│   │   ├── Rels.lean             # RelD → run function
│   │   ├── Props.lean            # RelD → Prop inductive, run-soundness theorems, audits (M2)
│   │   ├── Emit.lean             # the plan: groups, module assignment, module text
│   │   └── Main.lean             # `lake exe p4spectec-gen <export> --lib <Lib> [--update|--check]`
│   ├── Tactic/                   # the proof side (M2)
│   │   ├── RunSound.lean         # run_sound, run_sound_group: symbolic execution against the Prop
│   │   └── Audit.lean            # #audit_axioms
├── P4SpecTecTest/                # test-only: decode test, the differential runners (Diff/NanoP4Run/, Diff/NanoP4Interp/)
│
├── NanoP4Spec/                   # GENERATED, committed, diffed in CI; one module per Nano-P4 spec file, named as it
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
- JSON exports are committed. They are the OCaml/Lean contract, diff
  cleanly, and Lean builds do not need OCaml. CI checks they are current.
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

Rung 3 lives in: `IL/Ast.lean` and `Semantics/*` (reference side,
trusted), `Codegen/Types.lean` (value relations), `Codegen/Reify.lean`
and `Codegen/Validate.lean` (generation side), `Tactic/Refine.lean`
(proof side, where the real work is).

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
- **Unfinished work is a pushed branch**, never an uncommitted worktree.
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
- **Commits** follow Chris Beams' rules with a body that says why. Small
  self-contained changes go directly to `main`.
- **Independent read-only review after each step.**

## 9. Downstream use

p4blo (github.com/qobilidop/p4blo) is the motivating consumer: it wants
to prove its own architecture-free P4 IR semantics equivalent to
P4-SpecTec's, using this rendering. That is its problem to solve; this
project takes nothing from it. What a consumer of that kind needs from us,
and what we provide regardless of consumer:

- **A stable, versioned public surface.** Generated names, module split,
  the two relation encodings, and the per-relation lemma library are an
  API once imported. The naming rule is settled in the pilot and frozen;
  later changes are breaking. CHERI and Morello survived years of model
  changes only because lemma statements were generated with the model.
- **Extra spec files as ordinary input** (section 4.1).
- **Externs as parameters** through one interface (section 4.1).

## 10. Milestones

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
- **M4, P4Lib and the site.** BitVec bridge, packet types, first
  downstream proof, Verso site.

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
- Completeness direction of the refinement theorems: stated only where
  determinism is proved; whether to pursue it at all is decided after M2.
