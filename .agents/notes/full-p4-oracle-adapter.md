# Full-P4 boot and result oracle adapter

2026-09-25 checkpoint on `m3c-p4-oracle-adapter`, based on main `7d9d356`.
The adapter is a bounded M3C input/output oracle. It does not claim corpus
coverage, Lean agreement, target execution, or full-P4 proof coverage.

## Boundary and format

`scripts/export-p4-oracle.py` compiles `test/p4-oracle/probe.ml` against the
built P4-SpecTec gitlink and invokes it in two fresh processes, one each for
`Program_ok` and `Program_inst`. It rejects an upstream checkout whose HEAD
does not equal this worktree's indexed gitlink, whose tracked/untracked
source differs from the exact committed four-file export patch, or whose
current source fails to rebuild through Dune. The probe uses the CLI's
`Pass.algo` and `Backend_sim.Build.build` AL path with `cache=true`,
`det=false`, `guard=false`, then `Interface.parse_program` and
`Interp.eval_rel`. These are the calls behind `run -al` at this pin.
`eval_rel` clears call caches before dispatch. Both relations receive the
same independently booted typed IL value; the driver compares their full
JSON boot trees and refuses a mismatch. It does not feed `Program_ok`'s
output to `Program_inst`: upstream's latter relation calls the former.

The compressed `schemaVersion=1` JSON contains one `boot` value produced by
upstream's `Il.value_to_yojson`, plus each relation's exact output values
using the same serialization, result class, diagnostic and fresh counter
before boot, after boot and after evaluation. Classes are `pass`, `syntax`,
`unmatch`, `abort`. The public AL entrypoint collapses internal `Err` and
`Unmatch` into `Run.Unmatch`, so `unmatch` is an observable class only;
the adapter cannot recover that internal distinction. Unexpected OCaml
exceptions terminate the probe and fail export, rather than becoming a
passing or excluded case. No output is erased or alpha-renamed, including
literal `FRESH__` identifiers. The JSON is compact deterministic gzip and
stays ignored under `.artifacts/` unless a smaller, reviewed export policy
is chosen. The raw expanded basic-routing observation exceeded 500 MB;
its compact gzip was 907 KiB. Do not commit broad duplicate corpora.

The exporter accepts explicit absolute upstream, include, program and
output paths. Its input can be any source file, but `test/p4-oracle/check.py`
pins its p4c source with the nested upstream gitlink and requires a clean
checkout. The test hashes complete boot and output JSON after substituting
checkout path prefixes in known source-region fields with `$UPSTREAM`,
`$P4C`, `$REPO`. It leaves semantic text, identifiers, diagnostic messages
and ExternV JSON untouched. This keeps fixtures portable across directories
without ignoring notes or payloads.
The runtime gzip retains the original paths and exact upstream JSON.
Source-region paths, value IDs and hashes remain in the checked data.

## Bounded observations

`test/p4-oracle/observed.json` checks four inputs: the restored p4c
`basic_routing-bmv2.p4` sample, upstream positive `issue-212.p4`, upstream
negative `issue-204.p4`, and a tiny invalid P4 syntax fixture. For each it
checks boot digest, output digest and arity or diagnostic digest, class, and
counter checkpoints for both relations. The basic-routing sample returns
one `Program_ok` value and two `Program_inst` values, each fresh process
going from counter zero to 38. Both positive and negative regressions use
no fresh IDs; the negative is `unmatch` for both relations. The invalid
fixture fails in boot as `syntax`, with no boot value and counter zero.
The test separately runs the pinned `main.exe run -al` for every input and
relation, checking pass/fail parity. This is verdict parity, not a second
serialization path; the CLI does not expose result values or counters.
Diagnostic failures must exit 1 with empty stdout and nonempty stderr;
signals and other process failures never count as expected negatives.

Reproduce inside the pinned upstream Nix shell, with the sparse p4c restore
from `scripts/fetch-p4c.sh` already present:

```sh
nix --no-warn-dirty develop /Users/qobilidop/my/work/p4-spectec-lean#upstream --command python3 /Users/qobilidop/my/work/p4-spectec-lean-p4-oracle-adapter/test/p4-oracle/check.py --upstream /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec --p4c /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/.artifacts/p4c
```

The final four-case check exited 0, including the CLI parity check. A
standalone compressed export of the positive regression also exited 0.
The offline `test/p4-oracle/test_contract.py` suite exited 0 with twelve
tests. It mutates expected digests, output counts, counters and failure
classes; rejects missing, duplicated, reordered and empty cases; tests
malformed probe data and abnormal CLI exits; checks the exact patch/rebuild
contract; and distinguishes semantic path-like text from source locations.
Independent review of the first commit is filed in
`.agents/reviews/m3c-p4-oracle-adapter.md`; its four findings were fixed in
`997d0ab` and passed independent re-review with the twelve offline tests
and real four-case/eight-CLI check independently rerun (exit 0 each).
Publication branch `m3c-p4-oracle-publish` starts at current main `87e9181`
and integrates the reviewed changes without the earlier status snapshot.
Its ordinary gate requires the six adapter/test files and runs only the
twelve offline tests; it never fetches p4c or invokes the runtime oracle.
The frozen full integration gate exited 0 with no skips:

```sh
nix develop /Users/qobilidop/my/work/p4-spectec-lean --command /Users/qobilidop/my/work/p4-spectec-lean-oracle-publish/scripts/check.sh
```

The relocated publication tree also passed the real check (exit 0):

```sh
nix --no-warn-dirty develop /Users/qobilidop/my/work/p4-spectec-lean#upstream --command python3 /Users/qobilidop/my/work/p4-spectec-lean-oracle-publish/test/p4-oracle/check.py --upstream /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec --p4c /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/.artifacts/p4c
```

Root independently reviewed the integration gate changes and reran the
twelve offline tests and `bash -n scripts/check.sh` (exit 0 each), with no
findings. Only evidence documentation changed after the full gate; the
adapter/test code remains byte-identical to reviewed `997d0ab`. Remote CI
remains required before landing.
`--update` deliberately refreshes the small digest fixture after a reviewed
upstream or adapter change. An individual runtime export is:

```sh
nix --no-warn-dirty develop /Users/qobilidop/my/work/p4-spectec-lean#upstream --command python3 /Users/qobilidop/my/work/p4-spectec-lean-p4-oracle-adapter/scripts/export-p4-oracle.py --upstream /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec --includes /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/.artifacts/p4c/p4include --program /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/.artifacts/p4c/testdata/p4_16_samples/basic_routing-bmv2.p4 --output /Users/qobilidop/my/work/p4-spectec-lean-p4-oracle-adapter/.artifacts/p4-oracle/basic_routing-bmv2.json.gz
```

The current driver processes one program at a time and parses full typed
JSON in memory. Broader corpus work should stream or shard observations,
record exclusions and source counts, and connect these values to both Lean
runners. This checkpoint is only the upstream-side oracle boundary.
