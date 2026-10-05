# Full P4: generation state and remaining obligations

Active since 2026-10-04, when the user resumed M3 (decisions, "Scope and product").
M3 remains incomplete: the executable library is generated and builds, and nothing
about it is certified. No IL backend or broader redesign is scheduled.
[Corpus](corpus.md) owns input/replay constraints; [review](review.md) owns
the bounded historical evidence and its limitations. Sections below the first
were compacted on 2026-09-26 and still hold unless the first says otherwise.

## Executable generation (2026-10-04)

`lake exe p4spectec-gen exports/p4.al.json --lib P4Spec --update` writes the whole
library: 72 files, about 520,000 lines of Lean, 25.1 MB, of which quotations are 16.7 MB, executable
definitions 5.6 MB and codecs 2.1 MB. It is ignored and pinned by `P4Spec.manifest.json`
(decisions, "Staged explicit-state generation"). Measured on this machine (arm64 Darwin,
Lean 4.34.1, working tree of the commit that introduced it):

- Generation: 6.4 s, about 1 GiB peak resident memory.
- `lake build --wfail P4Spec check-p4-quotes p4-gen-replay p4-interp-replay` from no
  P4Spec artifacts: 234.7 s elapsed, 543.8 s user. Spec modules import one another in a
  chain, so elaboration is serial: `8.02-evaluation-relation` 49 s (122,719 lines; the
  50-member `Expr_eval` group pulls typing into the same module), `8.10.4-eval-call` 34 s,
  `1-syntax` 31 s, `4.0-ir-syntax` 30 s. C compilation runs in parallel (8.02 alone 53 s).
- With its quotations stripped, 8.02 elaborates in 20.6 s, `4.0-ir-syntax` in 19.3 s and
  `1-syntax` in 25.4 s: quotations are roughly 40% of the chain. Moving them to modules
  beside the chain is the known next reduction; not done, because 235 s cold (about 15 s
  warm in the gate) is not yet a bottleneck and Nano's layout would have to move with it
  or diverge.
- `check-p4-quotes`: 1,672 compiled quotations equal the decoded export (1,689 minus the
  17 `VarD`), 3.8 s.
- `P4SpecTecTest/Oracle/P4/Replay/replay.py`: both Lean legs match the pinned upstream
  observations for `Program_ok` and `Program_inst`: `basic_routing-bmv2.p4` and
  `issue-212.p4` pass with upstream's semantic outputs and exact fresh counters (38 for
  basic routing, 0 otherwise); `issue-204.p4` is rejected by upstream and both legs, where
  any Lean failure matches. The generated leg also requires the decoded program to encode
  back to the booted value. Nine observation mutations are rejected on each leg; on the
  generated leg the exhaustion one uses a stub, since generated recursion has no fuel.
  The generated leg takes 2.3 s for the bundle, the interpreter leg 3.3 s. Externs are
  upstream's placeholders. This is six relation runs, not corpus coverage.

Two defects blocked elaboration and were fixed in the generator (Nano output unchanged):
repeated constructor atoms beyond the second, and tuple decoding outside a recursive type
group. No casting, recursion or monotonicity failure occurred. The
retired `m3b-state-production` failure concerned proofs, not this executable text.

What the generated library still lacks, in dependency order:

1. Nothing more for M3B: every relation has its logical relation and an audited
   run-soundness theorem (below). Proof modules do not join the serial chain.
   Since 2026-10-05 the library includes the logical relations:
   - `P4Spec/Refinement/Relation/` has one module per relation recursion group (132
     modules, 256 relations, 6.2 MB), each importing the quoted spec and the modules of
     the relations it calls, beside the serial chain. With them the library is 203 Lean
     files, 31.3 MB, about 668,000 lines; `lake exe p4spectec-gen exports/p4.al.json --lib
     P4Spec --update` takes 14.7 s. (These figures predate the run-soundness modules;
     current ones are under "Run-soundness for every relation".)
   - `lake build --wfail P4Spec` with the chain already built and no relation module
     built: 202.8 s elapsed, 361.4 s user (this machine, the working tree of the commit
     that added them). Per Lake's module times, `Expr_eval`'s 50-relation mutual block
     takes 195 s, `Type_ok`'s 37 s, `Expr_inst`'s 26 s.
   - Getting there took two changes to the emitter, both measured on a scratch probe
     first. An auxiliary predicate for an iterated premise now joins the mutual block
     only when it mentions a relation of the group: `Cast_impl`'s block went from 101
     types to 18, and its module from not elaborating in 13 minutes at 7 GB (time in
     Lean's recursor and `below` constructions) to 13 s. Each complete attempt is now a
     named reducible definition that later constructors' rejected prefixes apply: before,
     93 to 95% of the large modules restated earlier attempts, and the relation text was
     30 MB taking 850 s of CPU.
   - Three emitter defects surfaced and were fixed (Nano output unchanged): substitution
     inside a quoted variable name, two rules of one relation with the same name
     (`SelectCases_match/cons-head-match` occurs twice upstream), and a name bound to a
     constant being treated as a variable alias.
   - Run-soundness (2026-10-05): the 14 relations that are nonrecursive and reach no
     recursive relation through relation premises each have a `run_sound` theorem in
     `Refinement/RunSound/`, proved by `state_run_sound` with the axiom audit, recorded as
     coverage claims and checked by `check-coverage --full-p4` (113 s in the gate, most of
     it replanning the export in the interpreter). Ten of them call recursive functions,
     whose calls are run equations in the relation; none needs `[Externs]`. Two first
     failed on a defect in the shared helper `projCases`: it took a class method such as
     `==` for a structure projection and destructured the wrong variable, after which the
     state tactic continued only in the first resulting goal. The helper is fixed for
     both tactics and every Nano proof still checks; the per-branch continuation is
     changed in the state tactic only.
   - Run-soundness for every relation (2026-10-05, later the same day): the 155 relations
     of the 31 recursion groups (sizes 1 to 50) are proved by `state_run_sound_group`, one
     induction over each group's least fixed point (decisions, "Recursive state
     run-soundness by fixed-point induction"), and with them the 87 relations that had
     been waiting on a recursive callee. `Refinement/RunSound/` has 132 modules, one per
     relation group, 0.5 MB; the library is 335 Lean files, 31.8 MB, about 680,000 lines.
     All 256 theorems are coverage claims; no relation carries a `runSoundness` exclusion.
   - Cost: with every other module built, `lake build P4Spec` took 401 s elapsed, 795 s
     user for the 132 proof modules (this machine). `Expr_eval` (50 relations, 321 rules)
     takes 185 s, `Type_ok` 52 s, `Expr_inst` 39 s, `Expr_eval_lctk` 21 s, every other
     module under 15 s. In `Expr_eval` 123 s is symbolic execution (79 s of it `simp`),
     16 s moving rejected attempts to the final functions, 5 s closing rules. The group's
     joint theorem has a heartbeat budget of 4,000,000 per relation. The proof modules'
     build products are about 387 MB, 161 MB of it `Expr_eval.olean`, which the CI `.lake`
     cache now carries.
   - What it took, in the order met. Each was first a failure or a timeout on a real
     group, and each is a rule of the tactics now:
     - Lean cannot derive `partial_correctness` for `Copy_out_inner` and the `Expr_inst`
       group (instance resolution on a long function type), so the induction is
       `fix_induct` on the group's fixed point with instances read off it.
     - `simp_all` erased facts obtained from an induction hypothesis and rewrote retained
       rejected attempts; `simp` on `<|>` rewrote inside rejected attempts.
     - Constructor search tried every earlier rule and compared every retained failure
       with every attempt: `Lvalue_read` went from a timeout past 140 s to 4 s once the
       path's rule is tried first and each attempt of the relation is a local definition
       named up front, against which a rejected alternative is compared once.
     - Unifying an attempt applied to metavariables with a rejected alternative took up
       to 121 s for one alternative (`TableEntry_keyset_simple_ok`, 134 s to 3 s after).
     - `assumption` on a function-call premise took a minute against another function's
       run equation (`V1Model_deparse`, 132 s to 1.5 s with a head-symbol filter; eleven
       architecture relations had timed out).
     - One `#audit_axioms` per theorem re-traversed the joint proof for each of a group's
       corollaries: `Expr_eval` went from 688 s to 185 s with one audit per group.
     - A relation without outputs binds a `Unit` result that no premise determines
       (`ConstructorType_wf`); it is assigned its one value.
   - Not done: the proofs say nothing about failing or diverging runs, and there is no
     converse. `Expr_eval`'s 185 s follows its 195 s relation module on the critical path
     of a cold build; splitting the step per relation into separate declarations would
     let Lean check them in parallel, untried.
2. Corpus replay on both legs (M3C): the 2026-10-05 sweep has both legs agreeing with
   upstream on 1,266 of 1,267 candidates ([corpus](corpus.md)). No native stack overflow
   or timeout occurred on the generated leg. Both legs also agree with upstream on its 37
   regression programs, 13 of them rejected. Open: the durable campaign with CLI parity,
   a committed mutation suite, p4c's own negative tests, and the one candidate above the
   case bound.
3. Refinement, representation and initialization certificates (M3E), all still stated
   for the pure ABI.
4. Targets (M3D) and determinism (M3F), unchanged below.

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

1. M3B: generate the unchanged export, resolve elaboration/casting/recursion
   failures, build every module with `--wfail` and audited run soundness,
   reproduce generation byte-for-byte, check full-P4 quotations and measure
   module timing. Done as of 2026-10-05: generation, the `--wfail` build of the
   executable library and of every logical relation, the manifest, quotations,
   timing, and audited run soundness for all 256 relations.
2. M3C: account for an explicit full-P4 corpus and exclusions, compare typing
   and instantiation verdicts and exact outputs on both interpreter and
   generated legs, resolve unexplained differences, and detect interpreter
   mutations. A both-leg sweep covers 1,266 of 1,267 candidates, and a second one
   upstream's 37 regression programs with its 13 rejections; see [corpus](corpus.md)
   for what they leave open. Type equivalence/substitution exhaustion and separate Type.Fresh
   effects constrain further coverage; current replay is bounded and guarded
   full-P4 coverage is not established.
3. M3D: independently validate actual packet targets, starting from bounded
   NanoSwitch work then v1model/eBPF STF cases. PSA syntax alone is no target.
4. M3E: expand audited refinement in dependency-driven slices (builtins,
   parameters, iteration, casts/subtypes, indexing/slicing/membership/externs),
   bring a real relation into coverage and benchmark the full environment.
   Mutation rejection and explicitly claimed scope are required; the
   all-definition claim stays open while any definition is excluded.
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
