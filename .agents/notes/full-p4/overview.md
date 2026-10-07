# Full P4: generation state and remaining obligations

Active since 2026-10-04, when the user resumed M3 (decisions, "Scope and product"). M3B
closed on 2026-10-05: the whole export generates, builds, matches its quotations, and every
relation has an audited run-soundness theorem against its generated logical relation.
Nothing about the library is certified against AL. No IL backend or broader redesign is
scheduled. [Corpus](corpus.md) owns input/replay constraints and evidence; [review](review.md)
owns the independent reviews and their limits. Sections from "Inputs and current
capability" on were compacted on 2026-09-26 and still hold unless the first says otherwise.

## The generated library (M3B, closed 2026-10-05)

`lake exe p4spectec-gen exports/p4.al.json --lib P4Spec --update` writes the library
(14.7 s measured before the run-soundness modules existed; not remeasured since): 335 Lean
files, 31.8 MB, about 680,000 lines, ignored and pinned by
`P4Spec.manifest.json`, sampled in `P4Spec.samples/` (decisions, "Staged explicit-state
generation"). Its parts, with measurements from this machine (arm64 Darwin, Lean 4.34.1):

- **Spec chain** (`P4Spec/<section>/...`, 72 modules, 25.1 MB, of which quotations are
  16.7 MB, executable definitions 5.6 MB and codecs 2.1 MB; 2026-10-04): every type with
  codecs and subtype bridges, every function, table and relation as an explicit-state
  executable definition, each with its quoted AL. `lake build --wfail` from no artifacts:
  234.7 s elapsed, 543.8 s user; the modules import one another in a chain, so
  elaboration is serial (`8.02-evaluation-relation` 49 s, 122,719 lines, the 50-member
  `Expr_eval` group pulls typing into it). Quotations are roughly 40% of the chain time
  (8.02 elaborates in 20.6 s without them); moving them beside the chain is the known
  reduction, not done while 235 s cold is not a bottleneck. `check-p4-quotes`: 1,672
  compiled quotations equal the decoded export (1,689 minus the 17 `VarD`), 3.8 s. Two
  generator defects were fixed for it (repeated constructor atoms beyond the second;
  tuple decoding outside a recursive type group); no casting, recursion or monotonicity
  failure occurred.
- **Logical relations** (`Refinement/Relation/`, 132 modules, 6.2 MB; 2026-10-05): one
  module per relation recursion group, beside the chain, each importing the quoted spec
  and the modules of the relations it calls. One cold build of them: 202.8 s elapsed,
  361.4 s user; `Expr_eval` 195 s, `Type_ok` 37 s, `Expr_inst` 26 s. The emitter choices
  this needed (free/tied auxiliary predicates, named attempts) are in decisions, "Shape of
  explicit-state logical relations"; three emitter defects were fixed (substitution inside
  a quoted name, two rules of one relation with the same name, a constant alias treated as
  a variable).
- **Run-soundness** (`Refinement/RunSound/`, 132 modules, 0.5 MB; 2026-10-05): a theorem
  per relation that a successful run from one fresh-identifier state to another implies
  the logical relation at those states, 256 coverage claims, no `runSoundness` exclusion.
  The 155 relations of the 31 recursion groups (sizes 1 to 50) are proved by one induction
  per group (decisions, "Recursive state run-soundness by fixed-point induction"). One
  build of the 132 modules with everything else built: 401 s elapsed, 795 s user;
  `Expr_eval` (50 relations, 321 rules) 185 s, of which 123 s symbolic execution (79 s
  `simp`), 16 s moving rejected attempts to the final functions, 5 s closing rules;
  `Type_ok` 52 s, `Expr_inst` 39 s, `Expr_eval_lctk` 21 s, every other module under 15 s.
  The joint theorem's heartbeat budget is 4,000,000 per relation. Build products: about
  387 MB, 161 MB of it `Expr_eval.olean`, which the CI `.lake` cache carries. Seven
  traps were met on the way, each first a failure or a timeout on a real group; they are
  in `docs/lean-pitfalls.md`, "recursive state run-soundness", the resulting rules of the
  tactics in the decision, and the before/after figures (`Lvalue_read` past 140 s to 4 s,
  `TableEntry_keyset_simple_ok` 134 s to 3 s, `V1Model_deparse` 132 s to 1.5 s, one audit
  per group 688 s to 185 s for `Expr_eval`) with the full prose at
  `0d78b6e:.agents/notes/full-p4/overview.md`. Two shared-tactic changes came with them:
  `projCases` no longer takes a class method for a structure projection (the state tactic
  then continues in every resulting branch), and an undetermined `Unit` result of a
  relation without outputs is assigned its one value.
- **Gate cost**: a cold `scripts/check.sh` took 1,634 s on 2026-10-05 (444 s at the
  14-relation stage, warm for the chain and the relation modules); warm, 398 s. `check-coverage --full-p4` is 150 s of that because it
  replans the 98 MB export in the interpreter; a compiled check would remove most of it.
  On the critical path `Expr_eval`'s proof module follows its relation module. Untried:
  one declaration per relation's induction step, which Lean would check in parallel, and
  smaller proof terms.

What the theorems do not say: anything about a failing or diverging run, the converse
direction, or any connection of either side to AL. Pure-mode certificates (refinement,
representation, initialization) are not emitted for an explicit-state specification.

## Inputs and current capability

P4-SpecTec pin: `8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3`.
The full export covers 108 source files / 33,446 source lines. Upstream
owns sorted recursive directory enumeration and excludes `include/`;
the exporter passes the directory directly. Top-level regions name 80 files,
which is provenance, not a final generated-module count.

`exports/p4.al.json.gz` stores the lossless 98,387,720-byte export (about
2.61 MiB compressed); raw SHA-256 is
`803d798c13ae102e6aa970f65dfd2313d9d9b4094cae745049d3418c1af11953`.
`scripts/spec-snapshot.py` verifies before extracting the ignored JSON.
Deterministic gzip omits timestamp/filename; it erases no regions or hints.
Nano's original 8,508,087 bytes similarly survive in its 244,303-byte snapshot.
This keeps inputs self-contained; compression loses text diffs and still
grows Git history. Revisit external checksum-pinned storage if upstream bumps
make size/churn costly; the 5 MiB tracked/indexed-file cap has no exceptions.
Checksums establish accidental-corruption detection, not authentication.

The unchanged machine-readable census stays at `.agents/notes/p4-census.json`
because tooling already owns that path. It uses the actual decoder,
dependency analysis, classifier and individual emitters. The snapshot has
1,689 definitions: 610 defined/2 external types, 17 metavariables, 700 defined
functions, 47 builtins, 2 external functions, 52 table functions, 256 defined
relations and 3 external relations. There are no raw callable-name collisions.

The census is an emission probe, independent of the generated library above; its
component results are unchanged:

| Component | Census result |
|---|---|
| Executable callable text | 1,055 / 1,055 emitted (and now built in `P4Spec`) |
| Inductive relation text | 0 / 256: the census probes the pure `Props` emitter |
| Instantiated subtype bridges | 567 / 567 emitted (and now built in `P4Spec`) |
| Print hints | 190 occurrences / 67 types validated |
| Production refinement eligibility | Zero full-P4 definitions |

Component emission is not a certificate. Diagnostics stop at each component's
first failure. The old pure-mode estimate of
138 / 1,008 bodied definitions was not a stateful proof. Bounded
`StateValidate` fixtures are separate; Nano retains 18 eligible definitions.

The callable graph has 865 components (234 recursive, 23 multi-definition);
types have 554 (32 cyclic, 11 multi-definition). Raw self recursion differs
from the emitter's mutual-block/alias decision. Largest callable groups are
`Expr_eval` (50), `Expr_inst` (30), `Stmt_ok` (18), `Type_ok` (14);
largest type groups contain 20 and 16 members. Historical M3A text volume
was 110,089 lines of independently emitted executable/Prop fragments,
excluding types, adapters, quotations and proofs. It does not describe the
current stateful proposition result or a final library size. Full-environment
proof/module timing remains required; Nano timing cannot predict it.

## Constraints learned from implemented slices

- All thirteen original `continueResult` bridge failures erased type
  arguments. Instantiate both sides and require equivalent payloads, matching
  upstream `runtime/type/sub.ml`; no covariant payload cast is justified.
  All 363 occurrences (105 injections, 129 projections, 129 checks) share the
  exact `_CONT` payload after substitution; checks are `MixopSC`, not
  `RecurseSC`. Preserve monomorphic names and structurally name specialized
  child namespaces from complete region-free type arguments. Free parameters
  and explicit function-type arguments remain rejected pending a binder scheme.
  Synthetic two-specialization fixtures cover a case absent from this pin.
- Print-policy checks cover 2,120 case origins and all 567 bridge pairs.
  Every hinted `CaseE` must identify a real variant/case. The full 190-entry
  table elaborates; twelve pinned observations exposed byte-escaping and
  ASCII-lowercasing bugs. This is static-note compatibility, not arbitrary
  decoded-note or hinted-print refinement. Preserve the separate printer
  contract obligation before widening the claim.
- The 152 updates contain 146 root/dotted paths and six root-index updates:
  four lists in `Lvalue_write`, two byte-text replacements. These component
  implementations preserve base/replacement/index order, hard bounds errors
  and exactly-one-byte text replacement. Nested index prefixes and slices
  remain rejected; neither appears at this pin. Earlier Unicode-text and
  pure-fresh placeholders are superseded, not pending implementation advice.
- Fresh state is below failure: rejected alternatives and negation consume
  IDs. Literal `FRESH__` names and signed-63-bit wrapping are observable;
  initialization is not an implicit reset. Uniform state and bounded fixtures
  exist, but production planning/Prop/refinement integration remains open.
- Upstream warns that `$sink<T>() : T` has no clauses. The emitted computation
  fails; intended use and reachability still need a full-P4 validation audit.

`check-quotes` independently compares the compiled Nano AST with the decoded
export: it erases only regions/hints and source `VarD` entries, preserving
notes, origins, input positions, constructor identity and order. It caught
the type `id.al` quoting function `$id`; separate lookup fixed quotation and
file placement. All 342 Nano definitions match and mutation checks reject
structural changes. The same comparison covers the 1,672 full-P4 quotations
(`check-p4-quotes`), without Nano's separate `VarD` and print-hint checks.

## Remaining exit obligations

1. M3B: closed 2026-10-05 (above).
2. M3C: account for an explicit full-P4 corpus and exclusions, compare typing
   and instantiation verdicts and exact outputs on both interpreter and
   generated legs, resolve unexplained differences, and detect interpreter
   mutations. The 2026-10-05 sweeps have both legs agreeing with upstream on 1,266
   of 1,267 p4c candidates and on upstream's 37 regression programs, 13 of them
   rejected ([corpus](corpus.md)); no native stack overflow or timeout occurred on the
   generated leg. Open: the durable campaign with CLI parity on the generated leg, a
   committed mutation suite for the sweeps, p4c's own negative tests, and the one
   candidate above the case bound. Type equivalence/substitution exhaustion and
   separate Type.Fresh effects constrain further coverage; guarded full-P4 coverage is
   not established.
3. M3D: independently validate actual packet targets, starting from bounded
   NanoSwitch work then v1model/eBPF STF cases. PSA syntax alone is no target.
4. M3E: expand audited refinement in dependency-driven slices (builtins,
   parameters, iteration, casts/subtypes, indexing/slicing/membership/externs),
   bring a real relation into coverage and benchmark the full environment.
   Mutation rejection and explicitly claimed scope are required; the
   all-definition claim stays open while any definition is excluded. The
   explicit-state certificates are not emitted (above).
5. M3F: discharge rule overlap/disjointness for determinism and distinguish
   counterexamples from unresolved obligations. Reverse realization and exact
   logical relations do not follow from run soundness or determinism.
   The bounded consumer is complete; broader clients and P4Lib remain M4.

The retired aggregate `m3b-state-production` at `925fdbf` (source integration
`1b2ac70`) still failed its second full-P4 casting proof at the unchanged
4M-heartbeat ceiling. It is a failed experiment, not retained main's result;
do not merge it blindly or raise budgets to disguise the obligation.
Committed recovery uses the local bundle under
`/Users/qobilidop/my/work/p4-spectec-lean-archive-20260926` and its
`RESTORE.md`/manifest. Ignored experiment artifacts were intentionally
discarded. See [archive recovery](../archive.md) for bundle verification details.

## Reproduction and historical provenance

Inside the respective pinned Nix shells, use `scripts/export-spec.sh p4
upstream/p4-spectec/spec` after rebuilding upstream; then unpack through
`scripts/spec-snapshot.py`, run `lake exe p4spectec-census exports/p4.al.json
--check .agents/notes/p4-census.json` and `lake exe check-quotes`.
These commands are reproduction instructions, not checks newly run in this
documentation compaction.

Complete source reports are recoverable at commit `968ad65`, under the former
`.agents/notes/full-p4-reconnaissance.md` and `full-p4-{corpus-prep,
corpus-replay-plan,corpus-worker,corpus-shards,oracle-adapter,interp-replay}.md`.
That history retains detailed measurements and commands against retired
worktrees; those paths and ignored logs are not assumed to exist now.
