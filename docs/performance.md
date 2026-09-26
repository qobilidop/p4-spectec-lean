# Performance

This project measures the cost of building generated Lean models and their
proofs. Execution speed relative to the AL interpreter is not yet measured;
we do not claim a runtime speedup.

## Recorded measurements

The [Nano-P4 elaboration snapshot](performance/nano-p4-elaboration.md) records
Lake's per-module build durations on 2026-09-25, using Lean 4.34.1 on arm64
Darwin. It is a historical measurement, not a benchmark of every later commit.

The snapshot sums to 860.6 seconds across 48 modules. This is **not elapsed
build time**: Lake can build independent modules in parallel. Refinement
modules are the most expensive entries, so changes to proof automation and
module dependencies deserve particular attention.

These durations include the work Lake reports for each Lean module. They do
not isolate kernel checking from elaboration, tactic execution or other build
work. They also do not measure the whole repository's clean build, peak
memory, incremental builds or P4 program execution.

## Reproduce a measurement

From the repository root, with the pinned toolchain available:

```sh
nix develop --command scripts/time-elab.sh NanoP4Spec
```

The script removes the selected library's Lean and IR build artifacts,
rebuilds it, and prints a Markdown report. Dependencies outside that library
may remain cached. Run it only with a known library name and with no other
build using the checkout. It changes ignored build artifacts, not sources.

Keep the printed report under `docs/performance/`, separate from this guide.
When refreshing a snapshot, record the source commit and dirty-tree status,
toolchain, hardware, operating system and build parallelism alongside it.
The retained 2026-09-25 report lacks the source commit, CPU model and job
count, so it cannot support a controlled before/after comparison. Preserve
that limitation rather than inventing provenance.

Timing runs are manual and are not a CI performance gate. A new build-cost
comparison should use matching machines, dependency-cache conditions and
parallelism. Measure wall-clock duration separately; do not infer it by
summing the module table. A runtime comparison additionally needs matched
inputs, execution modes and observable results for both implementations.

For the module-splitting and proof-cost design choices, see
[Scale](design.md#7-scale).
