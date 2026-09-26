# Pinned full-P4 corpus inventory

This first tranche inventories inputs; it does not execute AL or claim corpus
fidelity. Run inside the repository's pinned Nix shell:

```sh
nix develop --command python3 test/p4-corpus/test_inventory.py
nix develop --command python3 test/p4-corpus/inventory.py --upstream <absolute-patched-upstream> --p4c <absolute-clean-pinned-p4c> --check
```

Without `--check`, inventory.py regenerates the small committed manifest.
It reuses the reviewed exact upstream/export-patch and clean p4c pin guards.
The manifest records the verified snapshot's declared SHA-256, source byte
digests, symlink spelling, exclusion-file digests and exact exclusion
manifest/line references. Actual snapshot extraction remains the existing
checksum-verifying gate's job; this inventory does not decode the snapshot.

The complete accounting is 1,352 raw paths: eighteen include-directory
helpers omitted by upstream's collector, 67 static exclusions, and 1,267
canonical attempt candidates. All identities remain in the manifest.
One of 68 positive exclusion references is stale. Manifest ordering is
lexicographic by complete canonical path after collection, independent of
upstream's directory traversal ordering; shard assignment uses canonical
candidate index modulo shard count. Source paths are never resolved away
from their canonical symlink identity, and source corpora are not copied.

Standalone manifest validation rejects malformed identities, schema, counts,
exclusion references and digest corruption. `--check` additionally rebuilds
against pinned sources and requires exact equality. The inventory script
itself does not execute programs or provide resume behavior. The separate
bounded v2 pilot below provides observation contracts and a Lean worker;
helpers remain outside standalone program attempts.

## Separate v2 bounded pilot

The v2 probe and worker preserve all published v1 files byte-identically.
The probe records five distinct Type.Fresh phase counters per fresh relation
process; the worker labels any nonzero phase unsupported and validates all
fields first, even on syntax-only observations. It compares exact builtin
counters and semantic outputs, distinguishing hard-error/unmatch and fuel
exhaustion. A matched public failure means only agreement with upstream's
collapsed public failure class, not equality of its internal failure tag.

```sh
nix develop --command lake build --wfail p4-corpus-worker
nix develop --command python3 test/p4-corpus/test_contract.py
nix develop .#upstream --command python3 test/p4-corpus/run.py --upstream <absolute-patched-upstream> --p4c <absolute-clean-pinned-p4c>
```

run.py rechecks exact pins, source patch and inventory correspondence,
rebuilds the Lean worker and full linked upstream target, verifies/extracts
the AL snapshot, and checks the original four fixtures against their v1
summaries and eight known CLI exit contracts. It initializes one worker for
all four cases and real mutations, then another with zero fuel. Each worker
reads absolute case-file paths from stdin and emits structured one-line JSON;
EOF terminates it. Standalone usage is `p4-corpus-worker <spec.json> [--fuel N]`.
The Python driver establishes spec/source provenance; standalone operation
validates the artifact but does not independently prove a supplied spec's pin.

Bounds are separate: 120 seconds per upstream/CLI process, worker startup or
response; 32 MiB per uncompressed oracle/case output; 64 KiB stderr per child;
8 KiB per worker response; ten million fuel per relation; at most 32 cases
per worker object. The pilot closes workers before this count, and future
shard execution must recycle them. Python file-size polling can overshoot by
one polling interval before killing the process group; it is not an OS quota.
Lean checks file metadata, reads at most the byte bound plus one, rejects
changed length, and strictly validates recursive constructors/record fields.
Both boundaries reject duplicate JSON keys, including escaped spellings.

Ignored pilot directories contain deterministic per-case gzip observations
and an atomic small report with pins/hashes/resource settings and exact
selection, byte sizes, durations, typed phase sentinels and verdicts. Errors
after identity assembly leave an incomplete report with an explicit failure
kind; failed preflight stops before the report lifecycle. Neither becomes a
semantic verdict. The cumulative child RSS high-water metric uses platform
units (bytes on macOS), not a per-case measurement or hard memory limit.
The report is an execution identity, not yet a resume implementation.

This pilot is only the original four cases, six AL runs, one syntax-only
case and sixteen actual Lean mutations. It is not a small corpus shard,
whole-corpus coverage, generated-code replay or packet-target validation.

## Bounded shard and durable resume

`shard.py` is separate from the original-fixture pilot. It selects canonical
candidate index modulo shard count, revalidates pins/source/snapshot, rebuilds
the full linked upstream target and Lean worker, and records a strict identity
including actual executable bytes. An additive optional helper workspace key
keeps probe compilation paths stable; the default v1 PID recipe is unchanged.
Only shard 0 of 317 (four candidates) has been exercised in this tranche.

```sh
nix develop --command python3 test/p4-corpus/test_shard.py
nix develop .#upstream --command python3 test/p4-corpus/shard.py --upstream <absolute-patched-upstream> --p4c <absolute-clean-pinned-p4c> --shard 0 --shards 317
```

The same command resumes only the exact execution identity. A single-writer
lock protects descriptor-relative, known-name artifact access. Symlinks,
hardlinks, unknown paths and references outside the run directory are rejected.
Atomic file and parent-directory fsync commit each artifact/terminal record.
Resume validates every completed record and bounded gzip observation before
skipping it. Known interrupted writes/orphans are recoverably quarantined;
malformed completed artifacts fail loudly, never silently rerun. Terminal
harness failures without an observation have a separate explicit schema.

Resource failures remain denominator attempts, never matches. Syntax-only
records do not count as AL execution; unsupported Type.Fresh and exhaustion
stay distinct. CLI/worker byte metrics unavailable through existing helpers
are null. RSS is cumulative terminated-child high-water in platform units,
not per-case memory or a hard limit. Completed harness/run failures are not
automatically retried under the same identity. SHA-256 identifies accidental
corruption/provenance changes, not adversarial coordinated rewriting.
The four-case result is not whole-corpus, packet-target or generated coverage.
