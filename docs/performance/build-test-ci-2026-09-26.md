# Build, test and CI optimization snapshot

Measured on 2026-09-26 (America/Los_Angeles), through 2026-09-27 UTC.
These measurements concern build and verification cost, not P4 execution speed.
See [Performance](../performance.md) for interpretation.

## Environment and scope

- Apple M3 Max, 16 logical CPUs, 64 GiB RAM; arm64 macOS 26.6.2 (25G83).
- Lean 4.34.1, using the repository's pinned Nix environment and dependencies.
- Starting performance checkpoint: `2743c3b`. The retained census baseline binary
  was built from `29ddf22`; its compiler code was unchanged through `2743c3b`.
- Graph reachability: `859e8aa`; prepared proof rules: `19195eb`;
  stateful preparation: `60d74c9`; packet fixture copying: `c795c26`;
  concurrent mutants: `164e005`; packed JSON access: `b916f9c`;
  native dependency ownership: `4cba852`.
- Local comparisons used already-built dependencies and unchanged pinned inputs.
  They are not clean-build or kernel-only measurements. Source edits were frozen
  during each integration gate. Native CI runs use GitHub-hosted Ubuntu machines,
  whose scheduling and exact hardware are not controlled by this experiment.

## Matched local measurements

| Work | Before | After | Comparison |
|---|---:|---:|---|
| Full-P4 native census, graph change |83.10–84.47s|14.18–14.95s|Four ABBA executions; exact report checked each time |
| Full-P4 native census, packed byte access |12.96–14.24s|3.84–5.33s|Separate four-run ABBA comparison, with graph change already present |
| split_dataplane_parameters proof |63.37s|18.89s|Original generated file, existing axiom audit |
| directionless_trailing_p proof |55.06s|11.32s|Original generated file, existing axiom audit |
| update_fieldValue proof |45.64s|10.11s|Original generated file, existing axiom audit |
| Stateful refinement fixture |29.27s|8.07s|Unchanged complete StateForward test file |
| Mutation scheduling |24.35s|16.98s|Prepared tactics already present; identical result JSON |

The graph comparison had some concurrent proof profiling; the packed-access and
stateful comparisons were isolated from other benchmark/build processes. Short
runs vary, as the census range shows. Proof runs used
`lake env lean -Drefine_al.trace=true` on each original generated file, so they
include elaboration, tactic execution and kernel checking. No generated proof
body or axiom whitelist changed. Stateful runs used ordinary `lake env lean`.

Graph discovery now builds forward/reverse adjacency once per query. The JSON
scanner uses packed byte indexing, avoiding whole-buffer boxing for escape
lookahead. Proof tactics prepare fixed global simp rules once per invocation;
local facts remain fresh and simplification results are not cached. Mutation
cases run concurrently only after the complete baseline passes, preserving
separate timeouts, scratch isolation, rejection diagnostics and result order.

## Warm gate and dependency work

A complete local gate on the `4cba852` executable inputs took **51.52s** with
warm artifacts and exited 0. All 44 stages ran. Its library, unit-test, example
and executable build stages were warm; major remaining stages were mutation
replay 18s, completion/coverage/quotation 8s and census 4s (integer stage timings).
This is a single observed warm run, not a guaranteed latency.

Recursive test-library enumeration previously rebuilt nine oracle entry modules
under a second configuration. Each unit/oracle module now has one build owner.
The full gate still builds every oracle executable and runs every verification
stage; it reports named stage durations and actual exit statuses.

Native dependency cleanup removes all five refinement-tactic object files from
each of four executables: generated typing replay, coverage, quotation checking
and packet checking. Lake's imported-module query falls from 107 to 50 for typing
replay and 129 to 38 for the coverage launcher. The coverage child still imports
the entire compiled model; an explicit Lake prerequisite prepares it. A missing
compiled model root was rebuilt automatically by standalone `lake exe
check-coverage`, after which all 97 compiled claims passed.

## Remote observations

| Revision | Gate elapsed | Workflow elapsed | Build/cache context |
|---|---:|---:|---|
| `29ddf22` |19m56s|21m02s|Prior cache restored; Prelude change rebuilt dependents |
| `2743c3b` |6m11s|7m07s|Warm library/tests/executables; census 140s and mutations 185s |
| `19195eb` |8m11s|9m21s|Changed compiler/tactics; proof and native rebuilds |
| `b916f9c` |7m11s|8m28s|Low-level JSON change rebuilt broad dependencies |
| `4cba852` |4m02s|5m14s|Import cleanup rebuilt certificates, examples and affected executables |

These successful runs have different invalidation patterns. They show actual
workflow improvement but do not constitute a controlled clean-build comparison.
At `19195eb`, the three expensive proof jobs took 50s/33s/21s, compared with
281s/243s/194s in the older ordering run; job durations overlap and must not be
summed into wall time. At `b916f9c`, the census stage took 10s and packet contracts 1s.

Sources: [ordering run](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36281893597),
[warm baseline](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36283667100),
[first optimizations](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36284518064),
[packed-byte batch](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36285243949),
[dependency cleanup](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36285795982).

## Reproduction

Run repository commands inside the pinned Nix shell. The ordinary gate supplies
stage timings; measure its outer wall time separately. A matching census sample
uses the native executable after building it:

```sh
nix develop --command lake build --wfail p4spectec-census
nix develop --command .lake/build/bin/p4spectec-census exports/p4.al.json \
  --check .agents/notes/p4-census.json
nix develop --command scripts/check.sh
```

For before/after comparisons, keep source revisions, machine, toolchain, input
hashes, build-cache state and parallelism explicit. Build once, then use a balanced
before/after order for native binaries; retain every exit status and require
identical checked output.
Do not run another build or modify executable inputs during a measured gate.
