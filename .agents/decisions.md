# Decisions

The decisions in force, grouped by topic, each with its reason and the
date it was made. A register, not a diary: a superseded entry is
rewritten in place with the new date and reason; an entry whose subject
no longer exists is removed. A decision the design document already
settles is not repeated here.

## Pins

- **P4-SpecTec is pinned at `8c8e0c6f`** (2026-09-17, "Merge branch 'main'
  into gsoc-nano-spec"), the head of upstream's `gsoc-nano-spec` branch,
  which is `main` as of 2026-09-17 plus the Nano-P4 frontend, test corpus
  and nano-switch target. Reason: Nano-P4, the pilot, is not on `main` at
  the previous pin `2730cfd9` (it lives on that branch, ten `main` commits
  behind); the differential harness needs the nano frontend to boot
  programs and upstream's `check` as the oracle. CI accepts a pin
  reachable from `main` or from `gsoc-nano-spec`. Confidence: medium; the
  branch could be rebased. Revisit when Nano-P4 lands on `main`: return
  the pin there. Bumped by moving the submodule and re-running the exports
  and the mirror checks. (2026-09-25)
- **The Nano-P4 spec is a second submodule, `upstream/nano-p4-spec`, pinned
  at `60dfd991`** (2026-09-08), the commit P4-SpecTec's branch references
  as its nested `nano-p4/spec` submodule, from the public
  `pacokwon/nano-p4-spec`. Reason: P4-SpecTec's nested submodule uses an
  SSH URL, and the compiler takes spec files as inputs anyway (design
  section 4.1). CI checks the pin is on that repository's `main`.
  (2026-09-25)
- **Lean `v4.34.1`, Batteries `v4.34.0`, no Mathlib.** The current stable
  release at project start; Batteries at the matching minor. Bumped
  together. (2026-09-25)

## Build and test

- **Warnings fail the build via `lake build --wfail`, not via
  `warningAsError` in Lake options.** The option rewrites severities at
  log time, so a `#guard_msgs` test expecting a warning would see an
  error; `--wfail` fails the build without changing what tests observe. A
  `sorry` is a warning (`warn.sorry`), so it fails the build too.
  Reason: Batteries and lean-mlir practice; lean-mlir's `sed` flip of
  `warn.sorry` is the alternative to avoid. (2026-09-25)
- **Linters on package-wide: `linter.missingDocs`, `linter.unusedSimpArgs`;
  `missingDocs` off in the test library.** Docstrings are the cheapest
  audit aid for a project whose value is reviewability. (2026-09-25)
- **Tests are a library built by `lake test`** (`P4SpecTecTest`, globbed),
  not default targets, so `lake build` is the client build and `lake test`
  the full one. Every module is imported by its root, checked by
  `scripts/check-imports.sh`, so no proof or test is silently skipped.
  Reason: cedar-spec's lint driver exists for exactly this failure.
  (2026-09-25)
- **Axiom audit per theorem: `#guard_msgs in #print axioms` naming the
  exact set for hand-written theorems, `#audit_axioms` after every
  generated theorem.** `#audit_axioms` (`P4SpecTec/Tactic/Audit.lean`)
  fails unless every axiom is one of `propext`, `Classical.choice`,
  `Quot.sound`, so a `sorry` or `native_decide` (`Lean.ofReduceBool`)
  fails the build. Reason: the exact set differs between generated
  theorems (a theorem about a `partial_fixpoint` definition depends on
  `Classical.choice`, one about a plain definition may not) and the
  generator does not compute it; naming a wrong set would fail for the
  wrong reason. Hand-written theorems keep the exact-set check, LNSym
  and lean-mlir practice. (2026-09-25, revised the same day)
- **CI uses `lean-action` for toolchain and `.lake` caching only; the gate
  is `scripts/check.sh` in both places.** One command locally and in CI.
  The workflow also checks the upstream pin is an ancestor of upstream
  `main`. Reason: Aeneas's pin-is-forward check; cedar-spec's uncached CI
  is the alternative to avoid. (2026-09-25)
- **Mirrored modules keep upstream names, including `snake_case`; our own
  code follows Lean style.** Reason: the side-by-side audit is the
  point of mirroring; renaming to Lean style would break it. (2026-09-25)
- **File naming by provenance** (decided with the user 2026-09-25): a
  mirrored module sits at its OCaml file's path under `p4spec/lib/`,
  capitalised component by component (`Lang/Il/Ast.lean`,
  `Runtime/Value/Value.lean`, `Interface/Builtin/Texts.lean`); a
  generated module is its spec file's name verbatim; our own code follows
  Lean conventions. The path, not dune's module name, is the rule because
  upstream's module names depend on each library's dune stanza
  (`lang` uses qualified subdirectories, `runtime` and `interface` do
  not), while the path is invertible without reading them. The mirror
  check derives its pairs from the paths; a module of ours under a
  mirrored root declares "not a mirror". (2026-09-25)
- **The keyword list for name escaping is extracted from Lean's own token
  table by a script, never hand-written.** Reason: Aeneas's escaping bugs
  recurred until they did this. Escape with `«»` only for whole-identifier
  keywords or illegal characters. (2026-09-25)
- **Generated files carry a grep-able first line and a fixed option
  preamble**, and generated modules live in their own library. Reason:
  Aeneas, Sail and lean-mlir all converge on this. (2026-09-25)
- **Mirror checks are `scripts/check-mirror.py`**, comparing the
  constructor lists of each mirrored OCaml type with the Lean inductive
  of the same name, per type rather than per file, because a `mutual`
  block forces a declaration order the OCaml does not have. Polymorphic
  variant unions are compared against the flattened Lean inductive.
  (2026-09-25)
- **The differential harness is Python** (`test/diff/run.py`), driving a
  Lean executable (`nano-p4-run`) that decodes and runs; upstream's
  verdicts are recorded next to the exported programs, so the gate needs
  no OCaml. Reason: the harness only orchestrates and compares; recording
  the oracle keeps CI to one toolchain. Settles design section 12.
  (2026-09-25)

## Environment

- **Nix defines the environment; everything runs inside `nix develop`.**
  `flake.nix` has a default shell (elan, git, python) and an `upstream`
  shell (nixpkgs' default OCaml package set and P4-SpecTec's libraries).
  CI uses the same shells, with the Nix store, `~/.elan` and `.lake`
  cached. Reason: the user wants reproducibility maintained
  systematically; nixpkgs at the locked revision replaces an
  opam-repository pin. Lean stays on elan because nixpkgs lags releases.
  The default OCaml set (5.5.0 at the lock) is used rather than the 5.1
  set upstream's README names, because only the default set is in the
  public binary cache; the 5.1 set compiles the compiler and Jane Street
  core from source, over an hour on a laptop and on every CI runner.
  Upstream's dune-project requires only `ocaml >= 5.1.0`. Risk: newer
  OCaml, menhir (20260203 vs 20240715) or ppx_deriving_yojson (3.9.0)
  may not build upstream unchanged; the first M1 step is that build,
  and a package override in the flake is the fallback. Confidence: high
  in the approach, medium in the versions; revisit at the first upstream
  build. (2026-09-25)
- **`.envrc` and `.direnv/` are ignored by git.** direnv is a personal
  convenience, not project tooling; the flake is. (2026-09-25)
- **No license header per file.** The root `LICENSE` is enough; the user
  dislikes per-file headers. (2026-09-25)

## Generated code

- **Print with validated type-and-mixop policies, not a changed value
  representation.** All 190 hints decode; all 2,120 variant origins and
  567 bridge pairs preserve policy selection at the pin. Enforce these
  conditions, plus actual variant/case constructor notes, during codegen.
  Emit literal hint data and configure the interpreter from the source
  spec. Reject unsupported forms, bounds errors and incompatible policy
  changes. Reason: the runtime note selects the hint, but a static type
  note is observationally sufficient under the checked invariant; a
  mixop-only global table would conflate unrelated families. No change
  to `Rel` or refinement coverage is implied: arbitrary decoded notes and
  the printer-table contract still need M3C/M3E evidence. Confidence:
  high for the checked pinned scope; revisit if a new export violates
  policy compatibility. (2026-09-25)
- **Specialize variant bridges by full type applications.** The thirteen
  full-P4 `continueResult` failures were erased arguments, not different
  payload semantics. Match upstream `runtime/type/sub.ml`: instantiate
  both variants and require equivalent payload types. Preserve existing
  monomorphic names; a structural, region-free encoding of both argument
  lists names specializations in child namespaces. No hash collisions or
  encounter-order dependence. Free parameters and explicit function-type
  arguments remain rejected until an explicit binder scheme is needed.
  Reason: faithful handling of all observed pairs without silently
  conflating future specializations or inventing covariant payload casts.
  Confidence: high at the pin; revisit when an export needs polymorphic
  bridge declarations. (2026-09-25)
- **M3A is reconnaissance, not completion of full-P4 generation.** The
  user authorized the full export, capability census, independent quoted
  AST check and a concrete plan for the rest of M3. `P4Spec.lean` remains
  a placeholder until the generator accepts the unchanged full export.
  The subsequent phases and exit criteria are in
  `.agents/notes/full-p4-reconnaissance.md`. Reason: separate rendering barriers,
  interpreter fidelity, target behavior and proof coverage so progress
  cannot be mistaken for the thesis's all-definition claim. (2026-09-25)
- **Spec directory enumeration belongs to upstream.** `export-spec.sh`
  passes the directory directly; upstream traverses recursively in sorted
  order and excludes `include/`. Reason: full P4 is sectioned, Nano-P4 is
  flat, and upstream already defines a deterministic policy. Nano-P4's
  export remains byte-identical. (2026-09-25)
- **Commit spec AL snapshots as deterministic gzip with a raw SHA-256.**
  User approved replacing the proposed 93.83 MiB JSON with a 2.61 MiB
  lossless snapshot before its first commit. `spec-snapshot.py` packs
  without a timestamp or filename and verifies before unpacking the
  ignored working JSON; the gate does this without OCaml. No regions or
  hints are erased. Nano-P4 migrates forward to 244,303 compressed bytes,
  preserving its original JSON bytes and published history. Rewriting
  history would save only its 268,720-byte Git object, not 8.11 MiB.
  The gate rejects tracked/indexed files over 5 MiB, with no exceptions.
  Reason:
  preserve the self-contained frontend/Lean contract without nearing
  GitHub's 100 MiB file limit or requiring LFS. Compressed files lose
  ordinary text diffs and still accumulate history; revisit at upstream
  bumps if size or churn warrants external checksum-pinned artifacts.
  Confidence: high for this checkpoint, medium long term. (2026-09-25)

- **The compiler consumes the AL (`algo -json`), not the IL.** The AL is
  the IL after upstream's algo pass: binding analysis rewrites every rule
  and clause so that patterns are single-level, subtype injections are
  explicit `if e <: T` / `let x = e as T` premises, and joint iterations
  carry length guards; rule groups are split into a shared match and
  paths. That pass (2.6k lines of OCaml) is exactly the middlend that
  makes the spec algorithmic, and it is what the AL interpreter runs, so
  consuming its output keeps codegen boring and the rung 3 semantics
  aligned. The deep embedding mirrors `al/ast.ml` on top of `il/ast.ml`.
  Supersedes the design's "IL" wording, which the design now reads as AL.
  (2026-09-25)
- **Generated Lean is emitted as text, one module per upstream spec
  file, committed under `NanoP4Spec/` and `P4Spec/`, and is the build
  input.** CI regenerates from the exports and fails on any diff;
  `--update` refreshes. Files carry a grep-able header and are never
  hand-edited. Reason: Lake parallelism and incremental builds, IDE
  responsiveness, reviewable diffs, and generated files that mirror
  their sources; every prior art emits text, and Wasm's monolithic
  outputs are the scale warning. Supersedes the same-day decision to
  elaborate from JSON through a `spectec_import` command with a separate
  golden; that route bought nothing rung 3 does not already give.
  (2026-09-25, revised the same day)
- **Text is produced by the generator's own `Std.Format` printer, not by
  building `Syntax` and running Lean's formatter.** Reason: the formatter
  needs an elaboration environment and its line breaking depends on
  width heuristics; a direct printer is deterministic, diff-stable and
  keeps the 100-column limit. Keyword escaping still comes from Lean's
  own token table (`scripts/gen-keywords.sh`). Refines the design's
  section 4.1 wording. (2026-09-25)
- **A recursive group that spans several spec files is emitted in the
  module of the last file**, since a `mutual` block cannot cross files;
  every other definition stays in its file's module, and modules import
  each other in spec order. Nano-P4's typing relations form one such
  group. (2026-09-25)
- **Generated code is written in `Eval := ExceptT Fail Option` and every
  recursive group is a `partial_fixpoint`; no fuel.** `Fail` is `err |
  unmatch` (upstream's `Err` and `Unmatch` without traces), `none` is
  divergence, and `Eval.orElse` retries only on `unmatch`
  (`choose_sequential`), which is monotone; two monotonicity lemmas
  (`ExceptT.mk`, `orElse`, plus `notHold`) are all Lean needs beyond
  its own. A definition's type is `Option (Except Fail T)` with
  `ExceptT.run` around the body and `ExceptT.mk` around calls, because
  `partial_correctness` is derived only for `Option`-typed definitions.
  Pure variable bindings are `have`, since the monotonicity tactic cannot
  eliminate a match on a `let`-bound variable. Reason: the M1 fuel was a
  placeholder; `partial_correctness` is the induction principle the
  run-soundness proofs use, and Nano-P4's 20 recursive groups (12 of
  functions, 8 of relations) all pass the monotonicity tactic, the
  whole library building in 14 s. Supersedes the M1 fuel decision.
  (2026-09-25)
- **The `Prop` encoding mirrors the run function statement by statement.**
  One compilation of a rule path yields structured statements
  (`Exp.Stmt`); the run function renders them as a `do` block and the
  `Prop` constructor reads them as hypotheses in the same A-normal form
  (calls as `f args = some (.ok x)`, checks as `e = true`, rule premises
  as the relation applied), with pure bindings and pattern matches
  substituted textually at identifier boundaries and every variable an
  implicit argument typed by the AL's notes. Reason: the run-soundness
  proof is then a symbolic execution whose facts are the hypotheses
  verbatim, which one generic tactic closes for every relation of
  Nano-P4 (77 relations, 98 theorems); an encoding chosen for elegance
  would need a per-relation proof. Iterated premises take the `∀`-form
  the kernel accepts (design 5.3). Confidence: high for the sound
  direction; the completeness direction is M2's open point. (2026-09-25)
- **Equality and ordering on generated types go through their IL values**
  (`valueEq`, `valueCompare`, via the generated `ToValue` instance), not
  through derived `BEq`. Reason: Lean's `deriving BEq` on nested
  inductives produces an opaque (`partial`) function that `decide` and
  `rfl` cannot unfold, which M2's proofs would hit; value equality is
  also exactly upstream's `Value.eq`, which the interpreter uses for
  `=`. (2026-09-25)
- **Encoders are structural, decoders take fuel.** `toValue` is generated
  as a mutual block with one helper per nested container occurrence
  (lists, options, tuples, and spec types applied to group members),
  because structural recursion through `List.map` is not accepted;
  `ofValue fuel` recurses on the untyped value and is auxiliary. Value
  notes on generated values are dummies (`Value.varT "id"` without type
  arguments, id 0, hash 0): notes are performance devices upstream.
  (2026-09-25)
- **The naming rule is frozen at the end of M1** as `P4SpecTec/Codegen/Names.lean`
  documents: spec names verbatim, `«$f»` for functions, `R`/`R.run` for
  relations, constructors from mixop atoms joined by `_`, `τX` for type
  parameters, `«x*»` for iterated variables, and every reference to a
  generated type, constructor, function or relation qualified with the
  library name, because spec variables are conventionally named after
  their types and would shadow them. A generated module is named after its
  spec file verbatim (`NanoP4Spec.«3.2-bits»` from `3.2-bits.watsup`,
  directories as components), so listings sort in spec order and no
  mapping is needed; the quoted imports are confined to generated files
  and the library root. Later changes are breaking (design section 9).
  (2026-09-25; module naming decided with the user the same day)
- **An `extern syntax` is `ExternValue`** (JSON the target owns, as
  `ExternV` upstream) and **`extern dec`/`extern relation` are fields of a
  generated class `Externs`**, an instance-implicit binder on every
  definition that transitively calls one; target instances arrive at M3.
  (2026-09-25)
- **Per-file elaboration timing starts at M1**, with a tracked table
  (`docs/timing-nano-p4.md`, from `scripts/time-elab.sh`, regenerated by
  hand at checkpoints), and proof-checking time of generated theorems is
  measured from M2.
  Reason: Isabelle's SpecTec backend needed constructor-capping passes on
  Wasm, which is smaller than P4; Sail's RISC-V Lean output is 175k
  lines; encoding choices are cheap to change only early. Supersedes the
  same-day decision to wait for M3. (2026-09-25, revised the same day)
- **Recursion strategy: `partial_fixpoint` for every recursive group,
  structural recursion for none, never `partial`.** Reason: one proof
  principle (`partial_correctness`) for every group keeps the generated
  soundness proofs uniform; a structurally recursive definition would
  need its own induction principle and gain nothing, since the
  executable encoding is never used in a termination argument. The
  interpreter port uses the same monad with an explicit fuel instead
  (below). Supersedes the "structural first" ordering. (2026-09-25)
- **The interpreter port takes a fuel, one unit per call of its recursive
  block, in `Eval`.** Reason: the block has about forty mutually recursive
  functions with calls under `mapM`, `foldlM` and thunks, and its recursion
  is not structural; `partial_fixpoint`'s monotonicity proof over it is a
  risk with no benefit, since rung 3 inducts on the evaluation and an
  induction on the fuel is that induction; the fuel is the only place
  where the port's shape is not the OCaml's, and `none` reads as
  exhaustion. The value matcher and the type substitution take a fuel for
  the same reason (alias unfolding). (2026-09-25)
- **Three Lean-specific encodings from M1:** iterated premises as
  `∀ x ∈ xs` and definitional `Forall₂` (lean4#1964), `BEq` not
  `DecidableEq` on nested inductives (lean4#2329), numerics as `Nat`,
  `Int`, `Rat` with explicit conversions. Reason: Breitner's Lean branch
  of Wasm SpecTec hit all three. (2026-09-25)
- **Per-construct encodings instead of IL-to-IL passes**, listed in the
  design (section 5.4). Reason: passes would move the generated code
  away from the spec file it mirrors; the Wasm Rocq backend's default
  values for partial functions produced provably false lemmas, so
  partiality is `Option` with side conditions. (2026-09-25)

## Verification

- **Check the compiled quoted spec independently on every gate run.**
  `check-quotes` decodes the current Nano-P4 export and compares it with
  `NanoP4Spec.spec` using derived AST equality, with test-only instances
  ignoring regions and hint lists. Source `VarD` entries are omitted,
  like `Ctx.init`; type notes and all other fields and ordering remain.
  Reason: comparing reifier output to itself cannot catch a bad quote,
  and a cached `#eval` cannot notice a changed external JSON file. The
  check caught the existing type `id`/function `$id` lookup collision;
  separate maps now preserve type quotations and source placement.
  This is a test of quoting, not a kernel proof, and extends to full P4
  once its generated library builds. (2026-09-25)
- **The full-P4 census is checked but is not a successful compilation.**
  `p4spectec-census` probes individual emitters, so every component gets
  its own first diagnostic despite earlier global failures. The checked
  report includes raw type recursion separately from the generator's
  mutual-wrapper choice; type text estimates follow the generator's alias
  unfolding rules. Reason: actual emitter diagnostics are useful for work
  ordering, while successful text emission and syntactic proof eligibility
  establish neither elaboration nor correctness. (2026-09-25)

- **Rung 3 is proof-producing translation, and the theorem is a
  type-indexed refinement, not equality.** Per IL type a value relation
  between IL values and generated Lean values; per definition, related
  inputs and interpreter success imply shallow success with a related
  output; a fixed per-construct lemma library and a syntax-directed
  driver discharge it, with the recursive case from the definition's own
  induction principle. Completeness is a second phase, only where
  determinism is proved. Reason: CakeML, Cogent and certifying extraction
  all state it this way and none obtained `rfl`; equality cannot hold
  between untyped backtracking evaluation and typed total definitions.
  (2026-09-25)
- **The refinement theorem (rung 3) is stated over the interpreter port
  with `Refines`, one value relation `Rel v x := canon v = canon
  (toValue x)`, one table hypothesis `HoldsSpec Lib.spec ctx.global`, the
  guard off, an empty local function table, and every fuel; a recursion
  group by strong induction on the fuel.** Design section 5.1 has the
  statement. Reasons: canonical equality is one definition with one
  connecting lemma (`eq_iff_canon`) and a dozen inversion lemmas for
  exposure, where an inductive similarity would be a second definition
  to keep in step; `Refines` over defined results (failure kinds
  included) is what makes `else` groups and `does not hold` premises
  meaningful, and divergence refining anything is what makes every fuel
  provable; one `HoldsSpec` over the whole quoted spec avoids listing the
  transitive callees of every definition, so the theorems live in modules
  after the spec files, one per recursion group (`Refinement/`); the guard is
  instrumentation, not meaning. `canon` is not idempotent on `ExternV`
  (`Json.compress` is a `partial def` nothing can be proved about), so
  equality tests are aligned by the congruence `eq_of_canon`, not by a
  normal form. Confidence: medium; revisit if the full spec (M3) needs
  facts about externs or function arguments. (2026-09-25)
- **The driver tactic `refine_al` has no per-construct lemma library:
  the interpreter's own equation lemmas, unfolded one fuel level at a
  time by `simp`, are the lemmas; the generated side is walked by the
  rules of `Refine/Calc.lean`; a definition whose helper matches on a
  projection (conditional equations) is unfolded by name.** Reason: the
  design's per-form lemmas (`interp_var`, `interp_call`, …) would restate
  the interpreter, and every restatement is a second text to audit;
  computing the interpreter on concrete quoted syntax leaves only the
  pairing at effectful steps (calls, tests, results) to rules, which are
  a dozen. The cost is proof time per definition (seconds per definition
  at Nano-P4's size), recorded in the timing table. (2026-09-25)
- **The fragment rung 3 covers is decided syntactically
  (`Codegen/Validate.unsupported`), closed under callees, and reported in
  the generated module; nothing is `sorry`ed.** Outside at M2: type
  parameters, function-typed parameters, externs, calls of builtins,
  casts and subtype checks, iterated expressions with a body and iterated
  premises, indexing, slicing, path updates with indexing, membership.
  Reason: the design's "emit the theorem only for the supported fragment
  and list the rest" (section 5); the list is the M3 work order for
  rung 3. (2026-09-25)
- **Determinism theorems are generated only where the tactic `det`
  proves them: one rule path, no `else` group, no iterated premise, and
  every relation called is deterministic by theorem (closed under
  callees, like the refinement fragment); the others are listed with
  their reason.** 2 of 77 Nano-P4 relations qualify. Reason: with one
  rule path, determinism is `cases` twice plus the callees' theorems and
  injectivity of `some`/`ok`; with several, it needs a disjointness
  argument per pair of rules, which is its own proof per relation; an
  unconditional attempt fails the build on the first multi-path callee.
  Confidence: high for the mechanism, low that per-pair disjointness is
  automatable; revisit at M3 with the full spec's rule overlap measured.
  (2026-09-25)
- **Run-soundness is proved by one generic tactic, `run_sound`, and a
  recursive group's theorem by `run_sound_group` over Lean's
  `mutual_partial_correctness`.** The tactic executes the run function
  symbolically (the `Eval.run_*` lemmas, `split` on pattern matches with
  `cases` on the variable behind a projection, `subst`), turns every
  call of a group member into its relation by the induction hypothesis
  and every call of an earlier relation by its `run_sound` theorem, and
  closes the goal by the first constructor whose hypotheses are found in
  binder order. `run_sound_group` reads the principle's conjuncts and
  matches them to the generated statement by function, because Lean
  orders a group's members in its own way. Reason: a generated per-path
  proof script would be brittle to Lean's normal forms; a tactic that
  fails loudly on a shape it does not know is the check the design asks
  for (a theorem the tactic cannot close fails the build). The two
  debugging entry points `run_sound_execute` and `run_sound_close` drive
  it step by step. (2026-09-25)
- **Rung 3 is defence in depth, not a smaller trusted base.** It moves
  trust from the generator to the interpreter port, which is reviewable
  side by side with upstream and cross-checked by rung 2. Both line
  counts are measured and reported. Reason: Sail's authors note a
  translation's semantics is "effectively defined by this translation";
  the claim must be honest. (2026-09-25)
- **A generated per-relation lemma library** (inversion per rule,
  run-soundness, a determinism theorem attempt whose failures are
  reported as spec findings) is part of the public surface from M2.
  Reason: CHERI and Morello survived model churn only through generated
  lemma statements; determinism is what downstream equivalence proofs
  need and what upstream checks only dynamically. (2026-09-25)
- **The compiler is written in Lean.** The deep embedding must exist in
  Lean for validation, so generator and validator share one AST and one
  decoder; Lean's formatter and token table give canonical output and
  correct escaping; a Lean generator could one day be verified. Upstream
  adoption is not a criterion (the user, 2026-09-25). (2026-09-25)
- **The goal is stated as a thesis with four claims** (design section
  1): complete rendering with nothing opaque, agreement with upstream,
  a refinement theorem per definition, and a generated lemma library
  usable for proofs. Reason: the prior-art review found the design
  stated an instrumental goal with no success criteria; the thesis rests
  on P4-SpecTec's IL being algorithmic, which is what Wasm's backends
  lacked. (2026-09-25)
- **The differential harness reuses upstream's `excludes/` lists** for
  p4c programs P4-SpecTec cannot handle, rather than maintaining its own.
  Upstream is an input, not a downstream. (2026-09-25)

## Documentation

- **Markdown for design and working notes; doc-gen4 for API reference
  once there is a public surface; a Verso site at M4.** Reason: the
  current readers are the user and agents, who need docs readable in the
  repository without a build; API docs from docstrings are free once
  `linter.missingDocs` is enforced; Verso earns its dependency only when
  there are stable declarations for examples to cite. (2026-09-25)
- **The project website is one GitHub Pages site, built by one workflow
  in the Nix shell, in three stages.** (1) Until M1 has real
  declarations: no site; the README and `docs/design.md` are the site.
  (2) After M1: API reference from doc-gen4, in a separate Lake package
  under `docs/api/` that ordinary builds never touch, published under
  the `api/` path. (3) At M4: a Verso site (website genre) in its own
  Lake package under `website/`, holding the design narrative and a
  tutorial whose examples are checked against the frozen public surface,
  with the doc-gen4 output beside it. Verso and doc-gen4 are pinned to
  the tag matching `lean-toolchain` and bumped with it. Reason: a page
  claiming something about the generated code should fail to build when
  the claim stops being true; a site before there is anything to show is
  maintenance without benefit. Agreed by the user 2026-09-25.
  (2026-09-25)

## Process

- **Complete M3 autonomously in reviewed stages.** The user explicitly
  authorized all remaining M3 work and asked that routine decisions not
  wait for their return. Make reasonable reversible decisions, record
  their reasons and uncertainties for later review, and pursue safe
  alternatives when blocked. New authority is still needed for destructive
  history changes or a material relaxation of the agreed correctness
  claims. Reason: maintain progress without hiding consequential choices.
  (2026-09-25)
- **Choose subagent models by workload.** At the user's request, use
  GPT-6 Astra for demanding semantics and proof audits, GPT-6 Sol for
  bounded implementation/testing, and GPT-6 Luna for straightforward
  inventory checks. Match each assignment to its actual difficulty;
  do not restart useful running audits solely to change models.
  Reason: spend stronger reasoning where it affects correctness while
  keeping focused work efficient. Revisit based on observed task quality.
  (2026-09-25)
- **Select merges per PR, defaulting to preservation of useful commits.**
  User approved merge commits for coherent individual changes, squash
  for a single change spread across incidental WIP/fixups, and rebase
  only with an explicit linear-history preference. Reason: Git is the
  project archive; messages, stable commit references and logical change
  boundaries aid later investigation. PR #5 should use a merge commit:
  its implementation and subsequent workflow decisions are distinct.
  The user prefers no merge-strategy section in PR descriptions; this
  choice belongs to workflow policy, not the change narrative.
  This does not bypass review, remote CI or repository protections.
  (2026-09-25)
- **Make the existing commit-message convention explicit.** Retain
  Beams' style and the under-50-character subject, spell out 72-column
  prose wrapping and rationale, and adopt Git's emphasis on atomic
  changes and self-contained explanations. Reason: naming a guide alone
  did not prevent unwrapped bodies in recent commits. Apply prospectively;
  do not rewrite published history for cosmetic cleanup. Source links
  and actionable instructions are in `AGENTS.md`. (2026-09-25)
- **No git tags.** Compaction and archiving rely on git history alone;
  the user does not want tags. (2026-09-25)
- **PRs by default; direct-to-main only for trivial, non-behavioral
  maintenance.** User approved tightening the earlier small-change
  exception: small code changes can carry substantial risk. Code, proofs,
  dependencies, exports, build/CI changes and substantive policy use PRs
  with independent review and passing remote CI, in addition to the local
  pre-push gate. Routine typos, formatting and status updates may go
  directly to main. Autonomous completion does not require an additional
  human approval unless repository protections require one. Reason: test
  on Linux before landing and retain a coherent review record without
  unnecessary ceremony for trivial maintenance. (2026-09-25)
- **PR descriptions explain rationale, evidence and limitations.**
  Adapted from GitHub's reviewer guidance and Google's engineering
  practices at the user's request. The actionable policy and source
  links live in `AGENTS.md`, not a second instruction file or a verbose
  mandatory template. Reason: a PR must remain understandable without
  agent chat history; review guidance should be proportional to risk.
  (2026-09-25)
- **Keep PR AI disclosure to one short sentence naming agent and exact
  model.** User requested concise attribution, beyond commit trailers.
  Model names come from session evidence, not a configured default.
  Review claims elsewhere must still distinguish AI-agent review from
  human review. The actionable rule is in `AGENTS.md`. (2026-09-25)
