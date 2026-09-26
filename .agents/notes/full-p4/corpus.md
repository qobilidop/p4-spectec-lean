# Full-P4 corpus and replay boundary

Broader execution is paused. This consolidates retained constraints and
historical bounded checkpoints from 2026-09-25, not a fresh corpus run.
[Overview](overview.md) carries generation and milestone obligations;
[review](review.md) identifies independent evidence and limitations.

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

Other denominators stay separate: `p4_16_errors` was not restored; upstream
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
