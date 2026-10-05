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

1. Logical relations (`StateProps`, 256 relations) and state run-soundness. The emitter
   handles nonrecursive fixtures; recursive groups need the `RecursivePrefix`/`StateRules`
   motives turned into a generator. These modules must not join the serial chain.
2. A corpus campaign on both legs (M3C). The generated leg has no fuel: a diverging run
   does not return, so the worker needs a wall-clock bound, and deep recursion runs on the
   native stack.
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
   module timing. Done as of 2026-10-04: generation, the `--wfail` build of the
   executable library, the manifest, quotations and timing. Open: logical relations
   and audited run soundness, without which M3B is not closed.
2. M3C: account for an explicit full-P4 corpus and exclusions, compare typing
   and instantiation verdicts and exact outputs on both interpreter and
   generated legs, resolve unexplained differences, and detect interpreter
   mutations. The generated leg exists for the four pinned cases only. Type equivalence/substitution exhaustion and separate Type.Fresh
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
