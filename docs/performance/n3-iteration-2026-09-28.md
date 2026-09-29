# N3 iteration performance

Measured 2026-09-28 (America/Los_Angeles), through 2026-09-29 UTC.
This measures generation, proof compilation and validation, not P4 execution.
See [Performance](../performance.md) for interpretation.

## Environment and comparison

Apple M3 Max, 16 logical CPUs, 64 GiB RAM, arm64 Darwin 25.6.0; pinned Lean
4.34.1 and Nix environment. Lake used its default scheduling, with no parallel
Lean build or replay in this checkout. Baseline: `770e405`, which passed the full
local gate and [remote CI](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36525856029).
The optimized measurement used the executable inputs committed through `d28d3b8`
(catalog `2ee52b9`, normalization `c5974e7`, dependency split `fa522c6`). Neither measurement is a clean checkout build: core
and external dependencies were already built, while affected certificates rebuilt.
The rebuilt module sets differ because the optimization changes module boundaries.

## Observed rebuild costs

| Measurement | Repaired baseline | Optimized |
|---|---:|---:|
| Full local gate, elapsed | 1073.97s | 835.25s |
| Library/certificate stage, elapsed | 903s | 668s |
| Full gate, user CPU | 4271.05s | 4437.53s |
| Longest observed weighted Nano import chain | 839.67s | 596.59s |

Both full gates exited 0, with no skipped stages. The certificate stage was 26%
faster; the whole gate was 22% faster. These are single observed rebuild runs,
not a statistically controlled clean-build comparison or a promised latency.
The weighted import chain sums Lake's module durations along dependencies; it is
not elapsed build time. CPU work increased slightly as more modules enabled
independent scheduling.

A second full gate with warm build artifacts exited 0 in **118.93s**. Its largest
stages were completion/coverage/quotation (43s), import reachability (17s),
certificate mutations (16s) and completion-inventory contracts (12s). No checks
were skipped. This is a warm validation measurement, not a rebuild comparison.

The longest chain still runs through reverse `bin_eq`, `bin_op`, `Expr_eval` and
`Call_eval`. Reverse `bin_op` alone took 308s during the optimized concurrent build.
The forward chain can now proceed when its own callee is ready. `Expr_ok` took
210s forward and 226s reverse, versus 399s in the earlier combined module;
those per-module durations overlap and must not be added to estimate wall time.

Integrated `4e566fb` also passed [main CI](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36531246981).
Its Linux certificate stage took 2043s, versus 2110s at stabilization: 3.2% lower.
Both runs restored the same `ffc21e7` main cache. This smaller Linux gain is a
single-run observation with different rebuilt module boundaries, not a statistically
controlled comparison or a promised latency.

## Changes and limits

Forward and reverse certificates have separate dependency chains, with old paths
retained as import-only aggregates. Every theorem body and audit is preserved:
3,932 whitespace-normalized theorem chunks and 4,095 audit names matched the
baseline exactly, including multiplicities. The full gate checks compiled claims,
axioms, generation freshness, source identity, oracle agreement and mutations.

Normalization retains every selected rewriting fact and local definition in its
cache keys. It excludes only direct rigid proposition heads that cannot match
Lean's assumption-discharge path; aliases remain. Fact lookup indexes the local
context once instead of repeatedly scanning it. Matcher equations are realized
before downstream proof elaboration, including those in unfolding equations.

Domain generation uses the already-built representation catalog and resolves each
supported source contract once. Current native generation remained approximately
four seconds: three checks before were 4.08–4.14s, after 3.93–4.10s, all successful.
The small samples had different concurrent process conditions and do not establish
a throughput improvement. The important boundary is avoiding uncached recursive
planning when future domain patterns reach complex nominal types. A regression
requires catalog resolution and rejects a missing entry without falling back.

## Isolated replay experiments

The same saved, combined `bin_op` source from `770e405` was checked against built
imports, preserving both proofs and audits. With profiling enabled:

| Configuration | Elapsed | User CPU |
|---|---:|---:|
| Conservative cache baseline | 291.29s | 465.06s |
| Narrowed discharge-only key | 283.16s | 449.71s |
| Same narrowed key, native tactics | 262.60s | 413.08s |

Native execution improved the matching replay by 7.3%. These experiments precede
the final fact-lookup indexing and matcher pre-realization changes. Profile phases
nest: simp reported about 288s of accumulated work, so phases cannot be summed
as exclusive wall time. Simplification remains the largest cost.

A follow-up on the final executable tree (`4e566fb`, identical to `d28d3b8`)
replayed that same saved source: 288.39s wall / 457.52s user without native loading,
and 265.09s / 417.76s with it. Both exited 0. The final matched native improvement
was 8.1%; the ordinary replay remained close to the repaired baseline. This
supports dependency scheduling as the main source of the full-build improvement.

Exact structural sharing after simp did not help: 293.44s versus 291.29s, so that
experiment was removed. Native library preparation cost 26.77s for module libraries
and another 1.68s for the combined library, with existing Lean/C artifacts; this is
not a clean native build measurement. Native replay is opt-in. Attaching the entire
core native library to Nano builds would make Codegen edits invalidate unchanged
proofs, which would slow generator-only iteration.

## Reproduction and iteration

Run the full gate inside the pinned environment and measure outer wall time:

```sh
nix develop -c /usr/bin/time -p scripts/check.sh
```

After building imports, use the replay tool for a selected proof direction:

```sh
nix develop -c python3 scripts/replay-cert.py NanoP4Spec.Refinement.bin_op --only refines
nix develop -c python3 scripts/replay-cert.py NanoP4Spec.Refinement.bin_op --only refines --native
```

The tool expands aggregate names to actual proof sources. Directly elaborating an
aggregate file now only imports existing proofs; it is not a proof replay timing.
`--native` asks Lake for platform-specific shared libraries in dependency order.
With `--no-build`, stale or missing native artifacts fail instead of being rebuilt.
A live `empty_set --only refines --native` replay passed, including the build path;
a second `--native --no-build` replay also passed against current native artifacts.
Replay remains an iteration aid for tactic-only changes, not certification evidence.
Only the complete gate validates the integrated generated model.
