# Bounded shard/resume design

Bounded implementation, 2026-09-25; branch `m3c-corpus-shards` at merged main
`2c85f1b`. PR #22's Gate `36213412457` passed in 3m43s on `93a2e8c`.
Published inventory/v2 worker remain unchanged. Root approved this design,
four-case implementation/pilot and a narrow optional probe workspace key.
No whole-corpus launch is authorized. Independent frozen source/gate review
found no remaining findings after the bounded fixes below.

## Scope and first selection

Add `test/p4-corpus/shard.py` and offline `test_shard.py`, reusing the
reviewed inventory, v2 envelope and bounded subprocess/spec-once worker APIs.
Keep published v1 and original-fixture pilot byte-identical where possible;
no new Lean semantics or Type.Fresh state. CI wiring is separately reviewed.

First real pilot is the complete deterministic shard index 0 of 317, four
canonical candidates under manifest
`20aa1f7140be7cfe2b97404ee72bd2a60f2f49061fbebffe8418fd0390cdc071`:

| Candidate index | Canonical sample |
|---:|---|
| 0 | action-bind.p4 |
| 317 | inline-stack-bmv2.p4 |
| 634 | issue3650.p4 |
| 951 | pred1.p4 |

All names are beneath `p4c/testdata/p4_16_samples/`. Selection is mechanical,
not filtered by observed success. Only this four-case shard is launched
after review; other 1,263 candidates remain unattempted. The whole manifest
still accounts for eighteen omitted helpers and 67 static exclusions.

## Strict identity and bounded execution

Hash a canonical versioned identity: upstream/p4c commits and exact export
patch; verified snapshot and inventory hashes; worker/probe/harness/helper
source and actual executable hashes; Lean/Lake dependency pins; absolute
checkout/snapshot roots; complete selected case identities/source hashes;
relation/config/fuel policy and byte/time/worker-count limits. Hash the
identity into the run-directory name; existing identity must match exactly.
Do not merge records from different settings or relocate/normalize semantic
payloads to force a cache match. SHA-256 detects accidental mismatch, not
malicious coordinated rewriting or a cryptographic oracle attestation.

Recheck exact pins/patch/clean p4c, manifest correspondence and snapshot before
new/resumed execution; rebuild current worker/full linked upstream target.
Compile once, then use fresh upstream processes per relation, one case in
memory at a time. Preserve v2 five-phase Type.Fresh sentinel and exact
post-boot/final builtin state. Nonzero Type.Fresh stays unsupported.

Retain initial reviewed bounds: 120 seconds per oracle/CLI process or worker
startup/response, 32 MiB per raw observation/case, 64 KiB stderr, 8 KiB worker
response, ten million relation fuel and one worker recycled after at most
32 requests. Concurrency is one. No timeout/byte/fuel escalation silently
inside a resumed run; changing settings creates a new identity. Record
per-phase durations/byte counts and the cumulative platform child RSS
high-water mark, explicitly not per-case RSS or a hard OS memory quota.

## Crash-safe per-case lifecycle

Use a POSIX advisory `flock` on a retained run lock file: the kernel releases
ownership on process death, avoiding stale PID-lock guessing. Keep one writer.
Write unique temporary files in the destination directory; flush/fsync the
file, atomically rename, then fsync the parent directory. Run identity is
durable before any case starts; no summary is an authoritative completion log.

Per-case names are hashes of canonical identities, never unchecked path joins.
An fsynced attempt/phase marker distinguishes in-progress work from terminal
records. Write the complete deterministic gzip observation first, then an
atomic terminal record containing identity/case/attempt, artifact raw/packed
sizes and hashes, upstream classes/phase counters, actual Lean tags/statuses,
CLI contracts and resource/failure metadata. Only a terminal record backed
by validated durable artifacts counts as completed. Summary derives from
validated terminal records and cannot duplicate the canonical denominator.

Resume revalidates identity, exact selection, every terminal record and its
bounded gzip/JSON/schema/hash/artifact references. Corrupt/missing completed
artifacts fail loudly; do not silently rerun them as if absent. Validate a
final-name orphan observation too; malformed final artifacts are errors.
An interrupted attempt with only temporary data or a valid orphan is recorded
as interrupted, its known files quarantined recoverably, and its case retried
from fresh sessions. Preserve prior attempt diagnostics; no orphan is counted
as a semantic success. Completed harness failures are retained on ordinary
resume, not automatically retried or promoted. An explicit later retry policy
can be designed separately; initially a changed run identity is required.

## Taxonomy and fail-closed summary

Keep two axes, not one Boolean: upstream pass/unmatch/abort/syntax classes
and Lean matched/matched-public-failure/syntax-only/unsupported-Type.Fresh/
unsupported-abort/exhausted/output/state/outcome disagreement statuses,
including the actual Lean pass/hard-error/unmatch tag. Syntax-only does not
count as AL execution; public failure agreement is not internal-tag equality.

Harness timeout, signal/crash, output/resource limit, worker startup/protocol
failure and interrupted attempt are phase-labelled diagnostics, not semantic
verdicts. Resource failures produce durable terminal failures and allow the
next selected case after worker replacement; report/exit remains nonzero.
Malformed new/cached artifacts, impossible records or provenance mismatches
are hard run errors, recorded when identity already exists, never skipped.
The first pilot can honestly be a completed four-attempt shard with resource
failures, but cannot report full agreement in that event.

## Offline and real checkpoint

Offline tests cover identity/selection/settings mutations, truncated/wrong
hash/oversized gzip/JSON records, missing phase/counter fields, duplicate
case/result records, marker/orphan recovery and durable initialization failure.
Inject crashes before artifact rename, after it and before terminal commit;
resume must retry exactly unfinished cases without accepting corruption or
double counting. Check file/parent fsync and single-writer exclusion.

Then execute only the four selected cases, stop to report exact upstream/Lean
outcomes, phase timings, sizes, resource failures and resume/recovery evidence,
and request independent review. No full-corpus or packet/generated leg claim.

## Frozen bounded implementation and evidence

`shard.py` owns descriptor-relative, no-symlink/no-hardlink artifact IO,
single-writer flock, fsynced atomic writes, strict terminal semantic/harness
unions, exact observation references and bounded gzip/JSON validation.
Sixteen offline tests pass, including actual atomic-write fault injection,
death between quarantine moves (artifact first, fsync, marker last), terminal
record/artifact mutations, startup failure, final-worker crash, malformed
resume failure durability, unknown/symlink paths, persisted compiler-output
hardlinks and file/parent fsync.
Existing five inventory, seven v2 and twelve v1 offline tests also exit 0.
Text and diff-whitespace checks pass. Narrow gate wiring requires the two
new source paths and unconditionally runs these sixteen offline tests with
failure propagation; no real shard, upstream build, fetch or network is
added to CI. Root independently read the wiring/reran sixteen tests (exit 0).
The full local gate process exited 0 without skips; remote CI remains owed.

The authorized helper change adds optional lowercase SHA-256 `workspace_key`
to `compile_probe`; default still uses actual `os.getpid()`, with the same
compile command. No fake PID/module-global monkeypatch is used. The shard
locks its build directory and hashes probe/helper/compiler/version, linked
`.cmxa` and `.a` archive bytes, flake lock and absolute roots into the
workspace key. Full upstream target and worker rebuild remain mandatory on
resume; actual executable bytes remain in the run identity. Two fresh links
at a fixed test workspace yielded identical SHA-256
`0154b3ed3caa353f3f2af48b764962a97ae9de0675063b310acbf362266e1380`.
Old PID-workspace binaries contain a differing OCaml source-filename suffix
(`robe/92671/probe.ml` versus `robe/98530/probe.ml`), as well as differing
Mach-O UUID/signature bytes. No executable bytes are normalized. The
published v1 probe, fixtures/check/replay and v2 worker/pilot sources are
unchanged. The helper validates a real directory and every child as a
single-link regular file before copying and before compiler writes. The
separately authored hardlink follow-up was independently reviewed with
sixteen shard/seven v2/twelve v1 tests (exit 0); it protects persisted cache
redirections under cooperative locking, not hostile concurrent replacement.
Reviews: `.agents/reviews/m3c-corpus-shards.md`,
`.agents/reviews/m3c-corpus-shards-recovery.md` and
`.agents/reviews/m3c-probe-workspace-hardlinks.md`.

Fresh frozen pilot command (pinned upstream shell):

```sh
nix develop .#upstream --command python3 test/p4-corpus/shard.py --upstream /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec --p4c /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/.artifacts/p4c --shard 0 --shards 317
nix develop --command python3 test/p4-corpus/test_shard.py
```

Actual final-helper pilot exit 0, run
`901d53d9beb90fc96af06c434e9141522fc4d7b544f935e96ad1d99b7ad66104`:
four terminal attempts, eight upstream passes/eight actual Lean passes,
eight matched relations, eight CLI parity checks, no syntax-only,
unsupported, resource or harness failures. All Type.Fresh phases remain zero.
Probe executable SHA-256
`0c8ed850efbaa16f4afa61c7ab43ec8edd94633178587cacae6a39e17c0fb97f`.
Content workspace key
`8441fa2fb6e6f3c98dae57b3ab3062caa22f69eca0afeda5d64c07624f0de480`;
helper source SHA-256
`6f4ebca6020f36225fcb065c5885938a72b42d46689c2f634f9c8f486e986696`.

| Case | Raw / gzip bytes | Oracle ok / inst seconds | CLI seconds | Lean seconds |
|---|---:|---:|---:|---:|
| action-bind | 644,918 / 25,201 | 0.990 / 0.553 | 1.089 | 0.044 |
| inline-stack-bmv2 | 9,779,436 / 303,349 | 0.661 / 0.708 | 1.315 | 4.024 |
| issue3650 | 10,030,781 / 313,986 | 0.663 / 0.715 | 1.308 | 4.001 |
| pred1 | 1,197,126 / 38,901 | 0.542 / 0.544 | 1.099 | 0.071 |

Worker startup: 10.983 seconds. Byte metrics unavailable through the frozen
worker/CLI helpers are null, not invented zeroes; exact raw/gzip sizes and
oracle stdout/stderr lengths are recorded. RUSAGE_CHILDREN high-water at
case commits is 227,917,824 macOS bytes; this counts terminated children at
that point, not the still-live spec-once worker, and is not per-case RSS or a
hard memory quota. The summary explicitly states the cumulative metric's
limit. Only the four approved candidates have been attempted; other 1,263
remain unattempted. Exact same-command resume on the final helper exited 0
with the same run identity/probe SHA, no new case-session lines, all attempts
still one and all four terminal-record byte hashes unchanged. All four gzip
observation byte sequences also equal the pre-hardlink-fix pilot: only build
provenance changed. Builtin before/boot counters are all zero; final counters
are action-bind/pred1 zero, inline-stack-bmv2 22 for both relations, and
issue3650 24 (Program_ok)/28 (Program_inst), each exactly matched by Lean.
Final-helper logs stay ignored at `.artifacts/corpus-shard-final-pilot.log`
and `.artifacts/corpus-shard-final-resume.log`. The actual frozen full-gate
process (`nix develop --command bash scripts/check.sh`) exited 0 without
skips, including both 78-program Nano differential legs, 48 output contexts,
342 quotations, existing oracles/census and the new sixteen offline tests.
Log: `.artifacts/corpus-shard-full-gate.log`; actual process exit was observed
before root authorized the local commit. No larger selection or push is
authorized by this checkpoint yet; root owns publication/reconciliation.
