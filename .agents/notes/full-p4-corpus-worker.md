# Corpus-v2 bounded worker checkpoint

2026-09-25; branch `m3c-corpus-replay`, main base `e31c1e8`.
The inventory-only tranche was independently reviewed with no findings;
review `.agents/reviews/m3c-corpus-inventory.md`. Root independently reviewed
the bounded worker/driver and reran seven offline tests and the full pinned
pilot (exit 0, report `98530`), with no remaining blocking finding:
`.agents/reviews/m3c-corpus-worker.md`. No explicit corpus shard or scale-up yet.

## Scope and boundaries

New `test/p4-corpus/probe.ml`, `contract.py`, `run.py`, `test_contract.py`
and `P4SpecTecTest/Diff/P4Corpus/Main.lean`; lake adds `p4-corpus-worker`.
No published v1 source changed; the diff of `scripts/export-p4-oracle.py`,
`test/p4-oracle/` and `P4SpecTecTest/Diff/P4Interp/Main.lean` is empty.
Main modules are exempt from library-root imports under
the existing executable convention, and check-imports exits 0.

The probe samples the separate Type.Fresh tick before/after spec loading,
after simulator setup, after boot and after evaluation. Any nonzero tick is
explicitly unsupported in Lean. Malformed envelopes/results and recursive
values fail before that classification; no alpha quotient or counter merge
is introduced. Checked runtime substitution remains bounded as previously
documented. Exact semantic outputs/builtin counters remain compared.
Actual Lean hard-error/unmatch tags are reported separately; agreement with
upstream's public failure collapse is not internal-tag equivalence.

The spec is initialized once for ordinary pilot cases/mutations. Each
relation resets from its exact post-boot builtin counter. A subsequent valid
positive case after the mutations still matches, exercising worker isolation.
The zero-fuel mutation uses a separate spec-once worker.

## Frozen verification

Commands in the pinned shells:

```sh
nix develop --command lake build --wfail p4-corpus-worker
nix develop --command python3 test/p4-corpus/test_inventory.py
nix develop --command python3 test/p4-corpus/test_contract.py
nix develop .#upstream --command python3 test/p4-corpus/run.py --upstream /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec --p4c /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/.artifacts/p4c
nix develop --command bash scripts/check-text.sh
nix develop --command bash scripts/check-imports.sh
nix develop --command git diff --check
```

Each exited 0. Worker build: 84 jobs. Five inventory tests and seven v2
contract tests pass, including actual child timeout/oversize enforcement and
a forced worker-init failure's durable incomplete report. Root found that
initialization occurred before the guarded lifecycle; construction now occurs
inside it, so initialization timeout/crash is also recorded. Final fresh
pilot `92671` rebuilt current Lean/upstream sources and verified the snapshot;
ignored report `.artifacts/p4-corpus-pilot/92671/report.json` records hashes.
Six original AL runs match, one original syntax case is explicitly not AL
execution, eight CLI parity checks pass and sixteen actual Lean mutations
classify correctly. They cover changed builtin counter/output, malformed
boot/nested output/class, syntax mode/guard, signed range, missing/changed/
initial/out-of-range Type.Fresh phase, malformed nullary type constructor,
extra envelope field, duplicate object key and zero-fuel exhaustion.
Every original relation has all five Type.Fresh counters equal to zero.

The first pilot failed on an overly strict success-stderr check: upstream
prints its known `sink` elaboration warning even on exit 0/`passed\n`.
The success check now mirrors the independently reviewed v1 exit/stdout
contract, and records stderr hashes rather than rejecting warnings.
Unexpected exits/signals remain harness errors; an offline -9 regression
passes. That failed observation remains in ignored partial artifacts `86998`.

## Resource observations and limits

Final spec-once startup: 10.841 seconds. Case elapsed durations include two
oracle sessions, two CLI sessions, packing and Lean replay:

| Case | Seconds | Uncompressed bytes | Gzip bytes |
|---|---:|---:|---:|
| basic-routing | 19.072 | 30,858,825 | 933,699 |
| positive-regression | 2.282 | 906,416 | 32,099 |
| negative-regression | 2.113 | 153,137 | 6,392 |
| syntax-error | 2.118 | 925 | 318 |

Observed cumulative child RSS high-water: 1,674,264,576 bytes on macOS.
This is a platform child-process high-water metric, not per-case RSS or a
memory cap. The large positive case fits but is close to the 32-MiB bound.
Before scaling, report oversized/resource outcomes rather than hiding them.

Per-phase bounds are 120 seconds per oracle/CLI process and worker startup
or response; 32 MiB output/case; 64 KiB child stderr; 8 KiB response; ten
million fuel per relation; 32 case requests per Python worker object.
File-backed output is polled, so temporary disk size may overshoot before
kill; these are explicit harness bounds, not OS CPU/memory quotas. Lean
limits the actual read to bound+1 and checks metadata/length, preventing a
changed oversized file from silently slipping through its metadata check.

## Still owed

The authorized narrow CI wiring now requires nine corpus paths, runs the
five inventory/seven contract tests unconditionally, and builds the worker.
It never fetches p4c or runs the real upstream-dependent pilot. Gate wiring
review passed with no findings; the independent reviewer reran shell syntax,
five inventory tests and seven contract tests (all exit 0):
`.agents/reviews/m3c-corpus-gate.md`. The frozen
`nix develop --command bash scripts/check.sh` process exited 0 with no skips,
including both Nano differential legs, all existing oracles/census and the
new offline suites/worker build. Its actual process exit was captured before
publication; ignored log `.artifacts/corpus-worker-full-gate.log`.
Still owed: exact selected small shard and honest outcome/resource accounting,
resumable identity/record validation, then full canonical attempts only with
separate review. The current driver is a pilot, not a resume implementation.
Remote CI and publication remain pending; full corpus/generated/target claims
are not made here.
The NanoSwitch typed extern-method boundary root found is unrelated:
this worker evaluates only full-P4 typing/instantiation, not packets.
