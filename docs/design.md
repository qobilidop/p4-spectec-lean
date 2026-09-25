# p4-spectec-lean: design

Status: agreed design, 2026-09-24, revised 2026-09-25. No code yet.
Diagrams: https://claude.ai/artifact/XCUhcd9cSsC4qBu2TjkiUJ (private).

## 1. Goal

A compiler from P4-SpecTec's IL (internal language) to Lean 4, reusing the
upstream OCaml frontend and elaborator unchanged, with the translation
validated as strongly as is practical. Plus a small Lean library for P4
primitives that downstream verification projects can import without the
generated spec.

Two things come out of the compiler, from one pass:

- The P4 language semantics as Lean definitions: types, functions, and
  every relation in two encodings (an inductive `Prop` for proofs and an
  executable `Option`-returning function for testing), with a generated
  soundness theorem linking the two.
- A decoder that turns a parsed P4 program into a term of the generated
  program type, so individual programs can be evaluated and reasoned about.

The project is self-contained. It depends on upstream P4-SpecTec and on
Lean, and on nothing else. Downstream projects consume it; they do not
shape it (section 8).

## 2. Principles

### 2.1 Correct by construction first, proofs second

Every place a reviewer can confirm correctness by inspection is a place
that needs no proof. So the design maximizes those places and spends
proof effort only on what is left. Concretely:

- **The IL deep embedding mirrors `ast.ml` exactly.** Same type names,
  constructor names, constructor order, field order, and comments. One
  Lean file for the one OCaml file. A reviewer reads them side by side
  and needs nothing else.
- **The semantics port mirrors the AL interpreter's structure.** One Lean
  module per OCaml module (`ctx.ml`, `interp.ml`, `backtrack.ml`,
  `nondet.ml`), functions with the same names in the same order, each
  with a comment citing the upstream file and line. Where the OCaml has a
  helper, Lean has the same helper. No refactoring into a preferred
  shape.
- **Builtins and targets mirror their OCaml files**, one Lean file per
  file under `interface/builtin/` and `backend-sim/<target>/`, same
  function names.
- **Generated names derive from spec names by one documented, invertible
  rule.** Relation `Stmt_ok` becomes `Stmt_ok`; rule `Stmt_ok/if-then`
  becomes a constructor a reader can predict without running the tool.
  Mixfix atoms get the same treatment. No renaming for taste.
- **Codegen output is boring on purpose.** No optimization passes, no
  rule merging, no cleverness a reader would have to reverse-engineer.
  The output should look like what a careful person would write by hand
  from the spec.
- **The export is upstream's own serialization** where one exists, not a
  custom encoder. The IL types already derive JSON; the patch calls it.
- **Deviations forced by Lean are one named list** (section 5.3). Each
  entry says what changed, why Lean needed it, and where. Nothing else
  deviates.
- **Mechanical mirror checks where cheap.** A script extracts constructor
  lists from `ast.ml` and function names from the interpreter and compares
  them with the Lean files, so the side-by-side property is tested rather
  than trusted.

### 2.2 The repository is the only state

Work must be resumable by a fresh agent or person from the repository
alone. Conventions in section 7.

## 3. Upstream facts the design relies on

Source: https://github.com/kaist-plrg/p4-spectec and the P4-SpecTec paper
(arXiv 2608.00639).

- Pipeline: `.watsup` spec files → EL (parsed) → IL (elaborated) → SL
  (structured) → PL (prose). We consume IL.
- The IL AST is `p4spec/lib/lang/il/ast.ml`, 261 lines. Definitions are
  type defs, functions with clauses and premises, relations with rule
  groups, plus `extern` types/relations/decs, `builtin` decs, and tables.
  Most of it already derives JSON serialization.
- Every relation carries an input hint. Elaboration guarantees all outputs
  are computable from inputs with no existential search. Determinism is
  validated dynamically, not statically, so rule order matters for the
  executable encoding but not for the `Prop` encoding.
- Externs and builtins are declared but not defined in the spec. Targets
  (v1model, PSA, eBPF) supply them; upstream keeps them in OCaml under
  `p4spec/lib/backend-sim/`.
- The full spec is about 1.2 MB across ~80 files. Nano-P4, the GSoC
  educational dialect, is the pilot target.
- Upstream has three interpreters: AL (backtracking over IL rules, 64 KB,
  the faithful semantics), SL (87 KB), PL (90 KB). We port AL.
- Upstream's P4 frontend (`p4spec/lib/interface/p4/`) preprocesses, parses
  (Petr4-derived menhir grammar), and "boots" the program into an IL value.
  `p4spectec run -rel Program_ok -i p4c/p4include -p prog.p4` does this
  before interpreting.
- Upstream ships an experimental meta-circular spec (`spec-meta/`, ~65 KB):
  SpecTec's own semantics written in SpecTec. Not relied on; noted as a
  possible future source for the IL semantics.

Prior art for spec-DSL-to-prover backends (Ott, Lem, Sail, K, Wasm
SpecTec's Rocq backend on branch `coq` and Lean backend on branch
`lean4-wip`) are all unverified pretty-printers. The kernel typechecking the
output is the safety net. Nobody has a verified backend of this kind.

## 4. Architecture

### 4.1 Spec flow

```
OCaml (upstream, unchanged)                     Lean 4 (this repo)
spec files → Parse → Elaborate → IL ────┐
                                        │ elab --json  (our only patch)
                                        ▼
                                   p4.il.json ──FromJson──▶ P4SpecTec.IL (deep embedding)
                                                                 │
                                                                 ▼
                                                        P4SpecTec.Codegen (metaprogram, IL → Syntax)
                                                                 │ elabCommand
                                                                 ▼
                                                        P4Spec (generated)
                                                          types      inductive / structure / abbrev
                                                          functions  def f (fuel : Nat), total
                                                          relations  inductive R : Prop  +  def R.run : Option
                                                          class P4Spec.Target  (extern state, Call_ext, extern decs, builtins)
                                                          ▲ imports P4SpecTec.Prelude
                                                          ▲ instantiated by P4Spec.Targets.*
```

Decisions:

- Almost nothing in OCaml. The JSON dump is a small patch to upstream,
  intended to be upstreamed. Everything else lives in Lean.
- The compiler takes a list of spec files, not a fixed directory, so a
  consumer can add an architecture or a contract written in SpecTec.
- Codegen builds surface syntax with quotations and hands it to the
  elaborator. No text round-trip, readable output when pretty-printed,
  Lean resolves implicits, universes and mutual blocks.
- Mutually recursive spec functions take an explicit fuel argument so Lean
  accepts them as total and they stay transparent to proofs. No `partial`.
- Relations are emitted in both encodings from one pass, with a generated
  theorem `R.run i = some o → R i o`.
- Externs and builtins become fields of a generated class. Target instances
  are ports of upstream's OCaml target code.

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
  and upstream's parser is the one the differential tests trust. A Lean
  parser could come later as a verified replacement.
- Deep embedding first. A shallow embedding (P4 program → Lean functions)
  is a separate later compiler, proved correct against this semantics. Out
  of scope.

## 5. Verification and validation

Four rungs. We build rungs 1 to 3. Rung 4 is deliberately out of scope.

1. **Kernel checking.** Every generated declaration and theorem is
   kernel-checked. Build fails on any `sorry`, `partial`, or unproved
   termination. Warnings are errors. An audit target prints the axioms of
   every generated theorem under a guard, so a native-decide escape or an
   imported axiom cannot pass silently. Free.
2. **Differential testing.** Run the generated executable relations and
   upstream's interpreter on the same corpus; compare typing verdicts, IR,
   instantiation results, and output packets. Also run the Lean IL
   interpreter itself (on the deep terms) against upstream's on a subset,
   which directly tests the semantics port. Nothing here is proved. Runs in
   CI. Mutation checks on both sides: mutate codegen and require rung 3 to
   fail; mutate the semantics port and require rung 2 to catch it.
3. **Translation validation.** Requires the Lean formalization of the IL:
   a deep embedding of the IL AST plus an interpreter for it. For each
   definition `d`, codegen emits the shallow Lean definition `d` and the
   quoted IL term `⌜d⌝` (a structural copy of the JSON as Lean data), plus
   a theorem `⟦⌜d⌝⟧ = d` discharged by a generic tactic. A failing tactic
   fails the build. Codegen is therefore not trusted.
4. **Verified translation function.** Not practical: Lean's own elaborator
   is unverified. Not planned.

Rung 3 in plain terms: `d` is the fast generated code; `⌜d⌝` is the raw
spec kept as data; the interpreter is the slow, obviously-correct generic
walker; the theorem says the two agree on all inputs.

### 5.1 Trusted vs checked

| Component | Status | Why | Does not establish |
|---|---|---|---|
| Lean 4 kernel | trusted | standard | |
| Upstream parser and elaborator (OCaml) | trusted | defines what the spec means; shared with the official P4 spec toolchain | that the spec is P4 |
| JSON dump of the IL | trusted | tiny and structural; round-trip tested against upstream's IL printer | |
| `P4SpecTec.Semantics` (IL interpreter in Lean) | trusted | the spec of the compiler; mirrors upstream's AL interpreter file by file; cross-checked by rung 2 | agreement with SL or PL interpreters |
| `P4SpecTec.Prelude.Builtins` | trusted | ports of upstream builtins, one file per file; unit-tested against the originals | |
| `P4Spec.Targets.*` | trusted | ports of upstream target code; tested by the packet leg of rung 2 | that any target is a real device |
| `P4SpecTec.Codegen` | checked | every output validated by rung 3 | |
| Generated `P4Spec` | checked | kernel-checked, differential-tested, validated per definition | |
| Lean elaborator | checked | its output is what the kernel checks | |

### 5.2 The semantics port

The IL *syntax* is a mechanical constructor-for-constructor copy of
`ast.ml`. The *semantics* is a port of the AL interpreter, not a copy. The
core (expression evaluation, iterators, path updates, rule matching,
backtracking) ports function by function. What the port drops is
engineering, not meaning: mutable context, result caching, instrumentation
hooks, backtraces, and the unique-id value-equality scheme. Each omission
is an easy judgment call but not a mechanical one; that is what the
side-by-side review and the rung 2 interpreter comparison are for.

### 5.3 Deviations forced by Lean

The only places the Lean side does not mirror upstream. Each entry names
what changed, why Lean needs it, and where it lives. Anything not listed
here is a bug.

| Deviation | Why Lean needs it | Where |
|---|---|---|
| Fuel argument on mutually recursive functions and executable relations | Lean requires a termination argument; the spec's recursion is not structural | `Codegen/Funcs.lean`, `Codegen/Rels.lean` |
| Each relation emitted twice, `Prop` and executable | a `Prop` cannot be run; an executable function cannot be reasoned about declaratively | `Codegen/Rels.lean` |
| Structural equality for values | the OCaml unique-id scheme is a performance device tied to a mutable allocator | `Semantics/Ctx.lean` |
| No mutable context, caching, hooks, backtraces | pure functions; these are instrumentation, not meaning | `Semantics/*` |
| Mutual block grouping by dependency | Lean requires mutually recursive definitions in one `mutual` block | `Codegen/Funcs.lean` |

### 5.4 Test sources (all from upstream)

- p4c sample corpus: hand-written, mostly well-typed programs. Main source
  for typing and instantiation comparison; seed set for the fuzzer.
- Negative-test fuzzer (`p4spectec testgen`, `fuzzer/`): mutation-based
  generator of *ill-typed* programs, guided by spec coverage, reduced with
  creduce. Exercises the failure paths of the typing relation, where a
  first-match executable encoding and a backtracking interpreter are most
  likely to disagree.
- STF packet tests (`testdata/p4testgen/`): program + input packets +
  expected outputs, produced by p4c's p4testgen. Used by the packet
  simulation comparison.

There is no random well-typed program generator. Options if wanted later:
p4c's p4smith, or enumerating derivations of the generated inductive typing
relation. Not planned for the start.

## 6. Code organization

One Lake package `p4spectec` with several libraries. The core library and
root namespace are `P4SpecTec`, aligned with upstream. `SpecTec` alone
refers to the Wasm-DSL project and is not used as a name here.

```
p4-spectec-lean/
├── AGENTS.md                     # entry point for people and agents; reading order (no CLAUDE.md)
├── README.md
├── flake.nix                     # dev shell: Lean toolchain, OCaml 5.1 + opam deps, p4c includes
├── lean-toolchain
├── lakefile.toml                 # libs: P4SpecTec, P4Lib, NanoP4Spec, P4Spec; exe: p4spectec-emit
├── docs/                         # describes the artifact; never links into .agents/
│   └── design.md                 # this file
├── .agents/                      # describes the work; the resumable state
│   ├── status.md                 # current state only: evidence with commit hashes, open threads, next step
│   ├── decisions.md              # register of decisions in force, rewritten in place, with date and reason
│   ├── roadmap.md                # backlog beyond the milestones
│   ├── notes/                    # live working notes
│   └── reviews/                  # independent review reports for current work
│
├── upstream/
│   ├── p4-spectec/               # git submodule, pinned (brings p4c as its own submodule)
│   └── patches/
│       └── 0001-json-export.patch   # adds `elab --json` and `run --dump-value`, using the derived serializers
│
├── exports/                      # committed JSON: the OCaml → Lean handoff
│   ├── nano-p4.il.json
│   ├── p4.il.json
│   └── programs/                 # booted P4 programs used by Lean tests
│
├── P4SpecTec/                    # core library, language-agnostic
│   ├── IL/
│   │   ├── Ast.lean              # mirrors lang/il/ast.ml constructor for constructor
│   │   ├── Value.lean            # IL values (the `value` type of ast.ml, kept separate for the decoder)
│   │   └── Json.lean             # FromJson for both
│   ├── Semantics/                # TRUSTED: mirrors interp/interp-al/ file by file
│   │   ├── Ctx.lean              # ← ctx.ml
│   │   ├── Interp.lean           # ← interp.ml
│   │   ├── Backtrack.lean        # ← backtrack.ml
│   │   └── Nondet.lean           # ← nondet.ml
│   ├── Prelude/                  # runtime the generated code imports
│   │   ├── Num.lean              # nat/int arithmetic matching OCaml's Num semantics
│   │   ├── Iter.lean             # Option and List helpers for `?` and `*`
│   │   ├── Path.lean             # structural update along a path
│   │   ├── Subtype.lean          # `<:` checks, `matches` patterns
│   │   ├── Target.lean           # class shape for extern syn / rel / dec
│   │   └── Builtins/             # TRUSTED: mirrors interface/builtin/ file by file
│   │       ├── Call.lean, Extract.lean, Fresh.lean, Ints.lean, Lists.lean,
│   │       └── Maps.lean, Nats.lean, Numerics.lean, Sets.lean, Texts.lean
│   ├── Codegen/                  # NOT trusted: validated per definition
│   │   ├── Names.lean            # the one documented, invertible naming rule
│   │   ├── Types.lean            # TypD → inductive / structure / abbrev
│   │   ├── Funcs.lean            # FuncDecD → def with fuel; mutual block grouping
│   │   ├── Rels.lean             # RelD → inductive Prop + Option-returning run function
│   │   ├── Decode.lean           # FromValue instances for every generated type
│   │   ├── Reify.lean            # emits ⌜d⌝, the deep term as a Lean constant
│   │   ├── Validate.lean         # emits the d_valid and run_sound theorem statements
│   │   └── Command.lean          # `spectec_import [files]` elaborator command
│   ├── Tactic/
│   │   └── Validate.lean         # generic tactic discharging generated theorems
│   └── Emit/
│       └── Main.lean             # `lake exe p4spectec-emit`: pretty-prints generated Syntax to .lean
├── P4SpecTecTest/                # test-only modules: mirror checks, prelude vs builtins, decode round-trips
│
├── NanoP4Spec/                   # pilot: `spectec_import` of the Nano-P4 export + Targets/
├── P4Spec/                       # full spec, split per upstream spec section for build parallelism
│   └── Targets/                  # TRUSTED: mirrors backend-sim/<target>/ file by file
│       ├── V1Model/, PSA/, EBPF/
│
├── P4Lib/                        # independent of the generated spec; importable by downstream
│   ├── BitVec.lean               # lemmas bridging Int-mod-2^n spec ops to core BitVec
│   └── Packet.lean               # byte strings, header extraction and emission
│
├── test/
│   └── diff/                     # rung 2 harness
│       ├── run.py                # runs upstream interpreter and Lean binary on the same corpus
│       ├── compare.py            # normalizes and diffs verdicts, IR, packets
│       └── corpus.txt            # which p4c samples, fuzz outputs and STF files to use
│
└── scripts/
    ├── build-upstream.sh         # apply patches, build p4spectec at the pin; stamp records commit + patch digest
    ├── export-spec.sh            # regenerate exports/*.il.json
    ├── export-program.sh         # boot one .p4 file to exports/programs/
    ├── check-mirror.py           # constructor and function lists in Lean match the OCaml originals
    └── check.sh                  # every gate CI runs; exit code is the verdict
```

Choices embedded in the tree:

- Submodule plus patch, not a fork. Bumping upstream is one line.
- JSON exports are committed. They are the OCaml/Lean contract, diff
  cleanly, and Lean builds do not need OCaml. CI checks they are current.
- Generated Lean is not committed. The import command elaborates from
  JSON; the emit executable exists for reading and debugging.
- Trusted files are marked and each mirrors an upstream file. Only
  `Semantics/`, `Prelude/Builtins/`, and `*/Targets/` need side-by-side
  review against upstream.
- `P4Lib` does not depend on `P4Spec`. Target instances do (they
  instantiate a generated class), so they live next to the spec.
- The full spec is split per upstream section so Lake can parallelize and
  typing can be iterated on without rebuilding instantiation.
- Lake layout: importable modules under the root, test-only modules under
  a `Test` root, no Mathlib, one toolchain pin.

Rung 3 lives in: `IL/Ast.lean` and `Semantics/*` (reference side,
trusted), `Codegen/Reify.lean` and `Codegen/Validate.lean` (generation
side), `Tactic/Validate.lean` (proof side, where the real work is).

### P4Lib

Serves users of the generated semantics, not generation itself.

- `Packet.lean`: byte sequences, header extraction and emission. Needed by
  every target instance.
- `BitVec.lean`: the spec defines `bit<n>` arithmetic as unbounded-integer
  arithmetic modulo 2^n, so generated code computes with `Int`. That is
  correct but hostile to proof automation, which works on core `BitVec`.
  The bridge is a lemma library equating the two under the obvious
  conversion so goals can be handed to `bv_decide`. Needed by no rung; only
  by downstream proofs. Built last, driven by the first real proof.

## 7. Engineering conventions

- **`AGENTS.md` is the single entry point** and names every file an agent
  needs, in reading order. No `CLAUDE.md`; Claude-specific notes go in
  `.claude/rules/`.
- **`docs/` describes the artifact, `.agents/` describes the work.**
  `docs/` never links into `.agents/`; a test enforces it.
- **`.agents/status.md` holds current truth only:** last checked evidence
  with commit hashes and CI links, open threads, next concrete step.
  Updated at every checkpoint.
- **`.agents/decisions.md` is a register, not a diary.** Each entry has a
  reason and date; a superseded entry is rewritten in place; uncertain ones
  carry a confidence and a revisit trigger.
- **Compaction at milestone boundaries** rewrites status and decisions to
  what is true now, deletes finished notes, and promotes artifact-describing
  notes into `docs/`. Git history is the archive. No tags.
- **Unfinished work is a pushed branch** with a work-in-progress commit
  saying what it holds and lacks, never an uncommitted worktree.
- **Every external input is pinned and listed in one table:** P4-SpecTec
  by commit, the opam repository by commit, GitHub Actions by SHA, the Lean
  toolchain by version.
- **Gates are scripts; the exit code is the verdict.** The full gate runs
  before a push. A push is gated on a recorded exit status, never on a
  command that reads a log.
- **Proof trust is a build gate:** warnings as errors, an axiom audit over
  every advertised and generated theorem.
- **Commits** follow Chris Beams' rules; the body says why, not what.
  Agent commits end with a `Co-Authored-By` trailer. Small, self-contained
  changes go directly to `main`; multi-commit or build-affecting work gets
  a branch.
- **Independent read-only review after each step**, filed under
  `.agents/reviews/`, findings fixed on `main`.

## 8. Downstream use

p4blo (github.com/qobilidop/p4blo) is the motivating consumer: it wants
to prove its own architecture-free P4 IR semantics equivalent to
P4-SpecTec's, using this rendering. That is its problem to solve; this
project takes nothing from it. What a consumer of that kind needs from us,
and what we provide regardless of consumer:

- **A stable public surface.** Generated names, module split, and the
  shape of the two relation encodings are an API once imported. The naming
  rule is settled in the pilot and frozen; later changes are breaking.
- **Extra spec files as ordinary input** (section 4.1), so a consumer can
  add an architecture or contract written in SpecTec.
- **Externs as parameters** (the generated target class), so a downstream
  theorem can quantify over a shared extern model instead of reproducing
  any simulator's extern code.

## 9. Milestones

- **M1, Nano-P4, rungs 1 and 2.** JSON dump patch, deep embedding, codegen
  for types, functions and relations, prelude, mirror checks, differential
  tests against upstream on the Nano-P4 corpus. Naming rule frozen at the
  end of M1.
- **M2, Nano-P4, rung 3.** IL semantics in Lean, per-definition validation
  theorems, exec-to-Prop soundness theorems, generic tactic, axiom audit.
- **M3, full P4 1.2.5 spec.** Scale codegen and elaboration to ~80 files.
  Expect work on mutual blocks, fuel thresholds and build times. Target
  instances arrive with the packet leg of rung 2.
- **M4, P4Lib.** BitVec bridge, packet types, first downstream proof.

## 10. Open points

- Differential harness language: Python or a Lean executable. Leaning
  Python.
- Where the fuel threshold policy for executable relations lives; probably
  a small config next to each export.
- Whether upstream's meta-circular spec matures enough to generate the IL
  semantics from it. Would turn the side-by-side review into a diff against
  upstream, but one hand-written semantics stays at the bottom of the
  stack regardless.
- Which P4-SpecTec commit to pin first. Our own choice; the latest
  upstream commit that builds is the default.
- Lean version: current stable, Batteries, no Mathlib.
