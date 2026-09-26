# Bounded full-P4 corpus replay plan

Approved staged scope, 2026-09-25; inventory and bounded pilot are reviewed.
Shard/resume implementation remains a separately reviewed next step. Isolated
branch `m3c-corpus-replay`, initially based on main `c974c3d`. Reconcile the
reviewed replay/type parents after they merge; do not edit their frozen trees.

## Canonical denominator

Use the existing exact-pin p4c checkout absolutely, without copying sources:
`/Users/qobilidop/my/work/p4-spectec-lean-state-oracle/.artifacts/p4c`, pin
`6b7ec98e77dfc71c6e1309d9a76183cb31f35a8a`. Keep symlink path identity;
1,352 sample `.p4` paths comprise 1,347 regular files and five resolved
symlinks. This is a positive seed corpus, not a successful-oracle denominator.

Mirror pinned `Util.Filesys.collect_files` and `Util.Test.collect_excludes`:
sorted recursive traversal, exclude `include` directories, `.p4` suffix,
exact canonical `p4c/testdata/p4_16_samples/...` exclusion strings. Only a
literal leading `#` starts a comment; do not strip whitespace, inline
comments or match basenames. Static exclusions contain 68 unique positive
references, 67 matching paths: p4c=33, p4c-specific=25, p4-spec=10;
target-specific=0. The stale reference is `issue3291-1.p4`, from
`excludes/static/p4c/confirmed/i59-c5528-typevar-equals.exclude:1`.

The first executable inventory corrected this earlier raw-path assessment:
the upstream collector omits eighteen `fabric_20190420/include/**` helper
files. It collects 1,334 paths: 67 static exclusions and 1,267 canonical
candidates. Proposed complete accounting retains all 1,352 identities, with
an explicit collector-omitted/helper category for those eighteen paths.
The original 1,285 raw nonexcluded count is not the canonical upstream
attempt denominator. Root independently verified and approved this correction
before replay/scaling.
Report exclusion manifest/line/category provenance and the stale reference.
Dynamic STF exclusions, Nano's 78 programs, p4_16_errors, upstream regression
and simulator packet tests are different denominators, not implicit additions.

## Versioned fail-closed observations

Keep the published four-case schema-v1 oracle/replay unchanged. Add a
corpus-specific v2 probe/contract (sharing reviewed provenance/build helpers)
which records the distinct `Runtime.Type.Fresh.tick` before spec loading,
after spec loading, after simulator setup, after boot and after each relation.
Fresh relation processes retain cache=true, det=false, guard=false. Require
signed-63-bit counters, strict recursive Lean decode, exact semantic outputs
and builtin final counters. Until separately modeled, any nonzero type tick
is an explicit unsupported observation, never an alpha-normalized success.
Reject malformed/missing/changed sentinel fields in Python and standalone
Lean worker; include real Lean-side mutations. Syntax-only cases also validate
the full configuration/counter envelope but are not AL execution successes.

Source/build provenance remains the exact indexed upstream commit plus exact
allowed export patch, full linked upstream target rebuild, exact p4c commit,
verified AL snapshot hash, and exclusion-file hashes. Provenance is part of
the resumable run identity, not an informational header. No broad claim is
inferred from the six zero-tick checks in `type-fresh-reachability.md`.

## Bounded streaming and resume

Inventory first into a small deterministic manifest, assign sorted candidates
by stable index modulo shard count, and record selection explicitly. Compile
the probe once per run. Observe Program_ok/Program_inst in separate fresh
processes with per-process deadlines; signal, crash, invalid JSON and timeout
are harness outcomes, not upstream semantic classes. CLI parity uses only
known success/diagnostic exit contracts, never a crash-as-verdict rule.

Store each complete observation as a deterministic gzip under ignored
artifacts, atomically renamed with size/hash metadata. Process one case at a
time; no accumulated corpus boot-value array or 500-MiB bundle. Impose a
per-case decompressed-byte limit and record oversized cases explicitly.
Use a new Lean worker mode that reads case-file paths on stdin, initializes
the 98-MiB decoded AL spec once, and emits one strict structured verdict per
case. The current four-case runner hardcodes its names and reads a whole
bundle; preserve that API while extracting only shared checks needed by the
new worker. Reset each evaluation from its own exact post-boot builtin state;
recycle the worker after a bounded case count or failure. Parallelism starts
at one; independent shards permit later controlled concurrency.

Record resource parameters (timeouts, fuel, byte/case limits) in run identity.
Resume only after revalidating manifest, pins, hashes and completed case
artifact/verdict schemas; a truncated/corrupted record fails, never silently
skips or retries as success. Write atomic per-case records and derive the
summary from verified records. A failed shard can still provide honest partial
accounting but cannot claim a completed denominator. Disagreement, Lean hard
error, exhaustion, unsupported type state and harness resource failure remain
separate counts. Upstream public unmatch hides some error distinctions; report
that limit instead of manufacturing agreement on internal classifications.

## Staged implementation and evidence

1. Reviewed inventory/exclusion parser plus offline pin/manifest/shard/resume
   corruption tests; small committed manifest, not source corpus.
2. Versioned type-fresh probe/worker contract and original representative
   positive/negative/syntax cases, preserving v1 checks; real decoder/counter
   mutations and worker isolation tests.
3. A small explicitly selected shard, recording actual runtime/memory/byte
   observations and every outcome before scaling.
4. Full canonical-candidate attempt only after bounds and failure accounting are
   reviewed. Persist small checksummed summaries, not large observation blobs.

Proposed ownership: new `test/p4-corpus/` driver/probe/tests/manifest and
`P4SpecTecTest/Diff/P4Corpus/Main.lean`, narrowly shared replay validation
helpers only when necessary, roots/lake executable, working notes/status.
No check.sh edits until root separately reviews gate wiring. No external
source duplication, files over 5 MiB or whole-corpus claim before completion.
