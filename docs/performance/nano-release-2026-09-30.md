# Nano-P4 release costs

Measured 2026-09-30 (America/Los_Angeles) for the Nano-P4 milestone release.
This measures generation, proof checking and replay, not P4 execution.
See [Performance](../performance.md) for interpretation.

## Environment

Apple M3 Max, 16 logical CPUs, 64 GiB RAM, arm64 Darwin 25.6.0; pinned Lean 4.34.1
and Nix environment; Lake's default scheduling, with no other build in the checkout.
Lean sources were those of `034a90b`, which the later release commits change only in
Python, shell and documentation. Each rebuild removed one library's artifacts with
`scripts/time-elab.sh`; its dependencies stayed built. These are single observations,
not a statistically controlled comparison.

## Generation

Three runs of the generator's freshness check (`lake exe p4spectec-gen
exports/nano-p4.al.json --lib NanoP4Spec --runtime-extern value --check`), each
regenerating every module in memory and comparing it with the committed text:

| Run | Elapsed |
|---|---:|
| 1 | 4.16s |
| 2 | 4.13s |
| 3 | 4.10s |

## Proof checking

| Library rebuilt | Elapsed | User CPU | Module durations |
|---|---:|---:|---:|
| `NanoP4Spec` (generated model and certificates) | 696.92s | 4356.14s | 4797.9s over 1199 modules |
| `NanoP4Target` | 3.35s | 3.15s | 3.6s over 5 modules |
| `ExampleProofs` | 67.36s | 173.81s | 70.4s over 12 modules |

The summed module durations are not elapsed time; Lake builds independent modules in
parallel. The most expensive generated modules are unchanged from the
[N3 snapshot](n3-iteration-2026-09-28.md) within a few percent (reverse `bin_op` 317s
against 308s, forward and reverse `Expr_ok` 209s and 225s against 210s and 226s), and
the generated library's elapsed rebuild is comparable to that snapshot's 668s
certificate stage, which rebuilt a different module set. No regression needed
resolving. In `ExampleProofs`, the whole-program evaluation module takes 64s, almost
all of that library's cost.

## Replay and checking

A full gate with warm build artifacts at `868cc81` exited 0 in 255.46s elapsed (710.94s
user CPU), all 49 stages. Its largest stages:

| Stage | Elapsed |
|---|---:|
| Combined completion and mutation suites | 141s |
| Diagnostic and oracle executable build | 29s |
| Library layers and reachability | 22s |
| STF session replay, both Lean paths, 39 sessions | 14s |
| Completion inventory contracts | 12s |
| Typing replay, both legs, 78 programs | 6s |

The completion stage includes its own typing and session replays, `check-consumer`
and three mutation suites. During development, one warm run of the cross-layer suite
took 15.47s, and one replay of its forward proof about 5s (session observations, not
retained logs). The source-address filter suite took 22–43s in N5 runs, and the N3
snapshot's certificate-mutation stage (then the field-update suite) took 16s.
