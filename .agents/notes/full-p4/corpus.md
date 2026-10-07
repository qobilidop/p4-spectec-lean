# Full-P4 corpus and replay boundary

Active with M3 since 2026-10-04. The first section is the current corpus evidence; the
rest consolidates retained constraints and historical bounded checkpoints from 2026-09-25.

## Both-leg sweep (2026-10-05)

`P4SpecTecTest/Oracle/P4/Corpus/sweep.py --jobs 8` on the working tree of the commit that
introduced it (log and elapsed time in [status](../../status.md), summary under
`.artifacts/p4-corpus-sweep/`): exit 0. Of the 1,267 canonical
candidates, 1,266 were observed and both legs returned `matched,matched` for every one:
semantic outputs and exact builtin counters of `Program_ok` and `Program_inst`, upstream
class `pass` throughout, Type.Fresh ticks zero throughout. `switch_p4_16.p4` is unobserved:
one upstream session's output exceeds the 1 GiB bound (it exceeded 4 GiB in a scratch run).

What it took to get there, and what it shows:

- The first sweep had both legs disagreeing with upstream on the same two programs
  (`issue3531.p4`, `issue5231-const-int-concat.p4`), both through `static_assert`: the
  workers' placeholder externs made every extern relation a hard error, while upstream's
  `backend-sim/placeholder.ml` implements the compile-time `static_assert`. Ported as
  `P4SpecTec/BackendSim/Placeholder.lean` with `Core.Func.static_assert` and
  `find_var_value_t`; both legs use it (the generated leg through value codecs around the
  generated `$find_var_value_t`). No generator or interpreter defect was found.
- 81 candidates exceed the old 32 MiB case bound: 76 are at most 80 MiB, `fabric.p4`
  339 MiB, `up4.p4` 393 MiB, the two `dash` pipelines 866 and 926 MiB. The workers take the bound as
  `--max-case-bytes`; the sweep states 1 GiB. The shard campaign's reviewed 32 MiB limit
  is unchanged.
- Sensitivity: with `+ 1` changed to `+ 2` in the generated bit-slice width of
  `Lvalue_ok.run` (one line of `8.02-evaluation-relation`), 39 of the 1,186 programs under
  32 MiB disagreed on the generated leg (27 counter, 7 output, 5 outcome). The library was then regenerated; the rebuilt
  generated worker has the digest the sweep recorded. This was a manual check, not a
  committed mutation suite.
- Cost: capture dominates. In scratch runs before the committed tool, capture took about
  590 s for the 1,186 small cases at 8 jobs and 560 s for the 80 large ones at 6, and
  summed worker time was 1,132 s for the interpreter and 1,585 s for the generated leg,
  which is slower only on the largest programs (dash: 263 s against 46 s). A sample of
  `fabric.p4` shows the time in `valueEq`: generated `==` converts both operands to IL
  values on every comparison, here inside `$find_overloadeds_named`. Not a bottleneck for
  the sweep; it is one for any generated-leg target work. Options, none tried: a
  structural `BEq` proved equal to `valueEq` and installed with `@[csimp]`; comparing
  without materializing both values; caching the encoding of large immutable operands.
- The failed branch of `static_assert` had no upstream evidence in this set: upstream
  aborts, and no p4c sample fails. One error test exercises it (below).

Not established by this sweep: rejected programs (no candidate fails upstream; see the
regression and error-test sweeps below); internal failure kinds; `switch_p4_16.p4`; any
packet target.
[Overview](overview.md) carries generation and milestone obligations;
[review](review.md) identifies independent evidence and limitations.

## Regression sweep: rejected programs (2026-10-05)

`sweep.py --regression --jobs 8` on the working tree of the commit that introduced it
(`.artifacts/m3c/regression-3.log`): exit 0 in about 40 s. The candidates are upstream's
own regression programs at the pin (`8c8e0c6`), every `*.p4` under
`testdata/regression/{neg,pos,sim}`: 13, 4 and 20, 37 in all, candidate digest
`6ceb73e0…`. Both legs returned, per group: `neg` 13 of 13 `matched-public-failure` on
both relations, each leg failing with class `unmatch`, which is upstream's class for all
thirteen; `pos` 4 of 4 and `sim` 20 of 20 `matched` on both. These are the first
rejections in a swept set: twelve beyond `neg/issue-204.p4`, which the bounded replay
already covers on both legs, and the first three whose failure follows consumed fresh
identifiers (`issue-227`, `issue-236`, `issue-243`: counters 6, 4, 6).

The probe observes upstream's AL interpreter. Upstream's own regression harness runs these
programs in SL only, `neg` on `Program_ok` and `pos` on `Program_inst`; its committed
expectations (13 of 13 fail, 4 of 4 pass) agree with the AL classes observed here.

Limits:

- Every rejection is a typing failure. `Program_inst` has `Program_ok` as its first
  premise, and for all thirteen both sessions have the same class and counter; no
  instantiation failure after successful typing is exercised.
- For ten of the thirteen the counter after the failed run is zero, so any failure before
  the first fresh identifier matches; where a run fails is not compared, and a leg failing
  in the other class would also match (none did).
- The `sim` programs are used as accepted programs for typing and instantiation only;
  their `.stf` packet tests belong to M3D.
- The mutation suite below runs against this set.
- The p4c-corpus mode shares the changed capture code. It was rerun on the final tool
  (the cache identity changed, so every candidate was captured again): exit 0 in 1,240 s,
  1,266 of 1,267 `matched,matched` on both legs, `switch_p4_16.p4` oversized, as before.

## Error tests, sweep mutations and the generated-leg campaign (2026-10-06)

`sweep.py --errors` sweeps p4c's own negative tests, `testdata/p4_16_errors`, inventoried
in `errors.json` as the p4c samples are (584 programs; 49 excluded by 52 negative
references in upstream's static manifests, one of them stale; 535 candidates), which
upstream runs with `-neg` expecting every one to fail (its expectation file: 49 excluded,
535 failed, none passed). On the final tool (`.artifacts/m3c/errors-2.log`): exit 0 in
86 s, 535 of 535 observed, both legs agreeing on both relations:

| Outcome | Programs | What the legs did |
|---|---|---|
| `matched-public-failure` | 500 | failed typing in upstream's `unmatch` class at its counter |
| `syntax-only` | 34 | upstream's parser rejected the program; no boot, nothing evaluated |
| `matched-abort` | 1 | `issue3188.p4`: upstream's placeholder target aborted on a failed `static_assert` (counter 4); both legs fail with a hard error at that counter |

The abort case is the first upstream evidence for the failed branch of the ported
`static_assert`, which until now followed a reading of the OCaml only. Upstream's `abort`
class (any target-side error, here that one) was previously reported as
`unsupported-upstream-abort` without evaluating; the workers now evaluate it and match it
only with a Lean hard error at the same counter (`matched-abort`), since the port's
`Fail.err` does not separate a target abort from an AL error. The shard campaign accepts the same status. Limits: the 34 parser rejections
exercise no Lean code; where a run fails is still not compared; the 49 exclusions are
upstream's, not ours.

`mutations.py` is the committed mutation suite of the regression sweep (the Corpus README
has the table). It runs on the cached regression observations, requires the baseline to
pass exactly as the sweep does, and then requires each of six mutations to change the
outcome of exactly the expected programs to the expected statuses on the expected leg:
three mutated observations (counter incremented, outputs emptied, class turned into a
rejection, each on one accepted program, each caught on both legs), the generated
record-expression distinctness premise skipped (`neg/issue-207.p4`, the duplicate-field
program, becomes accepted on the generated leg: `outcome-disagreement` on both relations),
the interpreter's list concatenation reversed (every allocating program disagrees by
counter and every other accepted program by outcome, 27 of 37; the expectation is derived
from the observations, with the rule stated in the suite) and its fresh allocation
doubled (`counter-disagreement` on all 23 allocating programs). A code mutation is applied
in place, the worker rebuilt and run, the source written back byte for byte and the worker
rebuilt, which must restore its baseline digest; a build failure or an unrestored worker
is a harness failure. One run takes about six minutes (376 s), most of it the two rebuilds of
the generated module (`8.02-evaluation-relation`, which holds `Expr_ok`) and their
downstream chain. Not covered: mutations of the probe or of the p4c-corpus mode, and the
earlier manual bit-slice mutation, which the 37 regression programs do not exercise.

`shard.py --leg generated` extends the durable campaign to the generated worker: its
preflight regenerates and checks `P4Spec`, and the identity records the leg, the worker's
digest and the generated leg's adapter sources and library manifest. `--max-case-bytes`
and `--timeout` raise the reviewed 32 MiB and 120 s bounds (never lower them) and are
part of the identity. Both legs' bounds are read at the call, so the raised values reach
the oracle sessions, the artifacts and the workers. Run on the final tool
(`.artifacts/m3c/shard-{interpreter,generated}-1.log`): shard 0 of 64 (20 candidates,
indices 0, 64, ..., 1216) at 128 MiB and 600 s on each leg, exit 0, both complete and
okay, 40 relation matches each with CLI parity on every case, no harness failure
(identities `7190ca98…` and `a56659a8…` under `.artifacts/p4-corpus-shards/`). The
durable record therefore now has both legs, CLI parity and a bound above every
candidate but the four largest; the whole corpus still rests on the sweep.

## Inputs and canonical denominator

`scripts/fetch-p4c.sh` derives p4c commit
`6b7ec98e77dfc71c6e1309d9a76183cb31f35a8a` and HTTPS URL from the pinned
upstream gitlink and committed `HEAD:.gitmodules`. It restores shallow,
blob-filtered `p4include/`, `testdata/p4_16_samples/` and
`backends/ubpf/tests/testdata/` into ignored `.artifacts/p4c` without building
p4c or recursively initializing submodules. Reject dirty/wrong-pin/origin/root
destinations and symlink roots; do not substitute branch tips or duplicate
source in Git. Verify the actual repository root: `git -C` in an empty
submodule directory once silently reported parent commit `59525a2`.

The exact sample inventory is 1,352 paths (1,347 regular, five resolved uBPF
symlinks). Pinned `Util.Filesys.collect_files` skips eighteen
`fabric_20190420/include/**` helpers; 1,334 are collected, 67 statically
excluded, leaving **1,267 canonical attempt candidates**. Preserve symlink
path identity, source byte hashes and exclusion manifest/line/category.
The old raw nonexcluded count 1,285 is not the attempt denominator.
Inventory sorting for deterministic shards is not upstream execution order.

Mirror `Util.Test.collect_excludes` literally: only leading `#` is a comment;
do not strip whitespace/inline comments or match basenames, and read the final
line without newline. Of 68 positive static references (p4c 33,
p4c-specific 25, p4-spec 10), 67 match. Stale `issue3291-1.p4` comes from
`excludes/static/p4c/confirmed/i59-c5528-typevar-equals.exclude:1`.
All 60 exclusion files contain 120 static references (68 positive, 52 negative)
and 56 dynamic references (10 p4c, 46 p4c-specific); these are references,
not additive sample counts. Exclusions remain grounded in manifests.

Other denominators stay separate: `p4_16_errors` has its own manifest (above); upstream
regression has 4 positive, 13 negative, 20 simulator programs; p4testgen has
2,126 STF files but no P4 source; Nano has 78 programs / 39 STF files.
All literal includes resolved in the bounded restored sample tree, which does
not prove macro-expanded includes resolve or programs parse.

## Oracle, semantic comparison and v2 envelope

`scripts/export-program.sh` is Nano-specific and must not export full P4.
`scripts/export-p4-oracle.py` and `test/p4-oracle/` follow pinned `run -al`:
cache=true, det=false, guard=false. Verify indexed upstream pin, exact allowed
four-file export patch, clean exact p4c checkout and refreshed Dune linked
targets before probing. Separate fresh processes independently boot and run
`Program_ok` and `Program_inst`, then compare complete boot JSON. The latter
internally calls the former; chaining outputs or sharing counters changes
the source semantics. Parser value IDs, builtin fresh IDs and Type.Fresh ticks
are distinct state, never alpha-normalized or silently reset.

Schema-v1 retains typed boot/output JSON, literal identifiers, diagnostics,
classes and builtin counters before/after boot/evaluation in ignored
deterministic gzip. Only small digests are committed; normalization affects
known source/diagnostic regions, never semantic text, notes, IDs or ExternV
payloads. The four ordered cases are `basic_routing-bmv2.p4`, positive
`issue-212.p4`, negative `issue-204.p4`, and the syntax fixture. CLI success
requires exit 0 and exact success stdout; diagnostic failure requires exit 1,
empty stdout and nonempty stderr. Signals/crashes are harness failures.

Lean `p4-interp-replay` seeds each independent relation at the exact post-boot
builtin counter and compares every semantic `Runtime.Value.eq` output, arity
and final counter. Validate mode/config and signed-63-bit counters even for
syntax-only observations. Public upstream `Run.Unmatch` collapses internal
Err/Unmatch; agreement on that class is not internal failure-tag equality.
Fuel exhaustion and upstream abort are separate nonmatching results.
Syntax-only is not AL execution. Only P4 runner configuration implements the
pinned placeholder `init_objectState`/`init_archState` as null ExternV with
their correct notes; generic `Extern.none` is unchanged. This fixed positive
`issue-212` instantiation and implies no packet-target coverage.

Corpus-v2 (`test/p4-corpus/`, `p4-corpus-worker`) retains v1's API and records
Type.Fresh ticks before/after spec load, after simulator setup, after boot and
after evaluation. Any nonzero tick is unsupported. Validate strict recursive
typed JSON, all envelope fields and duplicate keys before classification;
malformed data cannot become unsupported success. The spec-once worker resets
each evaluation to its observed builtin counter, reports actual Lean tags
and preserves independent cases after mutations. Six zero-tick original AL
checks establish no whole-session type-fresh fidelity.

## Resource, identity and recovery constraints

Process one case at a time. Reviewed limits: 120 seconds per oracle/CLI or
worker startup/response, 32 MiB raw case, 64 KiB stderr, 8 KiB worker response,
10,000,000 relation fuel, one worker recycled after at most 32 requests,
concurrency one. File polling can overshoot disk limits before kill; Lean
reads at most bound+1 and checks actual length. These are harness limits,
not OS CPU/memory quotas. RSS is cumulative child high-water, not per-case
RSS; shard commit samples exclude a still-live worker. Missing byte metrics
are null, never fabricated zeros. Changing limits creates a new identity.

`shard.py` hashes source/patch/pins, verified snapshot/inventory, exact selected
case/source identities, actual worker/probe executables, linked archives,
toolchain/dependency pins, absolute roots and all configuration/resource
settings. Rebuild/revalidate on resume. A locked content-keyed compiler
workspace stabilizes path-sensitive OCaml bytes without normalizing binaries;
default helper callers retain real PID workspaces. Lake/source/root changes
invalidate earlier identities even if semantic observations would match.
Hashes detect mismatch, not coordinated malicious rewriting.

One writer holds retained POSIX flock. Descriptor-relative artifact IO rejects
symlinks, hardlinks and unknown paths. Unique same-directory temporary writes
are file-fsynced, atomically renamed and parent-fsynced; identity is durable
before cases start. Complete gzip precedes the terminal record, which records
identity/attempt, raw/packed hashes/sizes, phases, semantic tags, CLI contracts
and failures. Only validated terminal records backed by bounded validated
artifacts skip execution; summary is derived, not authoritative.

Interrupted known temporary data or valid orphan observations are quarantined
recoverably and retried from fresh sessions. Move/fsync the observation first,
retain the attempt marker until moving it last, preserving interruption
history across a second crash. Corrupt final artifacts fail loudly; never
silently rerun them. Completed resource/harness failures remain terminal on
ordinary resume and count as attempts, not semantic matches. Resource failures
can continue after worker replacement but keep a nonzero result; invalid
protocol/provenance stops the run. Final worker failure remains sticky even
after a successful final reply. Retry-policy changes need separate design.

Compiler cache entries must be real single-link regular files before source
copy and again before compiler writes. This protects persisted redirects under
cooperative locks, not hostile concurrent filesystem replacement. Crash tests
inject exceptions/state transitions; they are not power-cut durability proofs.

## Bounded historical evidence and remaining work

v1 final adapter `997d0ab`: four observations/eight CLI checks and twelve
offline tests independently passed. Interpreter `5657373`: six booted relation
matches, one syntax-only case, nine real Lean mutation rejections and six
offline tests passed independently. Basic routing finishes each relation at
builtin counter 38; regressions/syntax use zero. Expanded v1 basic-routing
observation exceeded 500 MiB; compact gzip was about 907 KiB. Do not scale
its in-memory bundle to the corpus.

v2 pilot independently repeated as report `98530`: six AL matches, one
syntax-only case, eight CLI checks, sixteen real Lean mutations and valid
post-mutation replay passed; seven offline tests passed. Author final pilot
`92671` measured 10.841s startup, basic-routing 30,858,825 raw / 933,699 gzip
bytes (near 32 MiB), and cumulative child RSS 1,674,264,576 macOS bytes.
An earlier pilot `86998` failed because successful upstream stderr contains
the known `$sink` warning; success now checks exit/stdout and records stderr
hashes. That is a recorded failed harness experiment, not a semantic failure.

The selected shard 0/317 contains indices 0/317/634/951:
`action-bind.p4`, `inline-stack-bmv2.p4`, `issue3650.p4`, `pred1.p4`, under
`p4c/testdata/p4_16_samples/`. Manifest hash:
`20aa1f7140be7cfe2b97404ee72bd2a60f2f49061fbebffe8418fd0390cdc071`.
Final-helper run identity:
`901d53d9beb90fc96af06c434e9141522fc4d7b544f935e96ad1d99b7ad66104`.
It exited 0 with four terminal attempts, eight upstream/Lean passes, eight
relation matches/eight CLI checks, all Type.Fresh phases zero and no resource
or harness failures. Final builtin counters were respectively 0/0, 22/22,
24/28, 0/0. Startup was 10.983s; raw cases ranged 644,918–10,030,781 bytes,
gzip 25,201–313,986. Exact resume exited 0 with no new sessions, attempts
remaining one, and identical terminal hashes; root independently reran resume.
This four-case checkpoint leaves 1,263 candidates unattempted **at that
checkpoint**, not necessarily throughout later retired experiments.

Later historical corpus code `c4a8858` and partial campaign summaries are
recoverable from the local archival bundle; ignored raw campaign artifacts
were discarded, so exact campaign resumption is unavailable. Partial totals
must not be relabeled canonical-denominator completion. Existing identities
cannot be promoted across source revisions. On any future authorized resume,
restore inputs and establish fresh identities, review resource/failure
accounting, then attempt a separately approved selection. Full corpus,
generated leg and target claims remain open.

Reproduction entry points are `scripts/fetch-p4c.sh`,
`test/p4-corpus/inventory.py --check`, `test/p4-oracle/check.py`,
`test/p4-oracle/replay.py`, `test/p4-corpus/run.py` and
`test/p4-corpus/shard.py --shard 0 --shards 317`; supply current absolute
upstream/p4c paths and use the pinned upstream Nix shell for real observations.
The historical state-oracle checkout path is retired, not a current input.
Ordinary CI runs offline contracts/builds, never downloads or real shards.
Exact old commands, detailed metrics and source hashes are recoverable at
`968ad65` in the seven former full-P4 notes listed by the overview.
