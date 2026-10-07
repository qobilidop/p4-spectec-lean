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

The [build/test/CI optimization snapshot](performance/build-test-ci-2026-09-26.md)
records matched local hot-path measurements, native dependency reductions and
observed remote gate times. It distinguishes warm gates from rebuilds and
retains the measurement limits.

The [N3 iteration snapshot](performance/n3-iteration-2026-09-28.md) records the
repaired baseline, independent proof dependency chains, domain-planning boundary,
and optional native replay measurements.

The [Nano-P4 release snapshot](performance/nano-release-2026-09-30.md) records
generation, proof-checking and replay costs separately at the Nano-P4 milestone
release, and compares the expensive generated modules with the N3 snapshot.

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

## Profile a slow generated proof

A generated proof module that takes minutes is usually one phase of its tactic, not the
kernel. Copy the module to an ignored scratch file and add, before its namespace:

```lean
set_option p4spectec.stateRunSound.timing true   -- phases of state_run_sound(_group)
set_option profiler true
set_option profiler.threshold 500                -- milliseconds
```

then run `nix develop --command lake env lean <scratch file>`. The timing option prints
one `state_run_sound: <phase> <n> ms` message per phase: `execution` (the symbolic
execution of one relation's run, within which `transport` moves a retained failure to
the final functions and `fold` restates it as its named attempt) and `rule` (closing one
rule, within which `prefix` closes its rejected prefix); the group tactic also reports
`<member> unfolding`. Sum only the top-level phases (`execution`, `rule`, `unfolding`)
and compare with the elapsed time: whatever is unaccounted for is in the commands around
the proof, such as the audits, not in the proof. The profiler's cumulative table then
says how much of the tactic time is `simp` and how much of the total is type checking.
Record before/after figures with the module and the machine when a change is made for
speed.

For the module-splitting and proof-cost design choices, see
[Scale](design.md#7-scale).
