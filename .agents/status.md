# Status

Performance implementation complete, checkpoint 2026-09-29. Reviewed implementation
through `d28d3b8` is integrated on `main` at `4e566fb`, with passing full local gates
and [CI 36531246981](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36531246981).
This final evidence-only checkpoint preserves those executable inputs. Published
N3 history is preserved. N0/N1/N2 are complete; N3 remains incomplete. N4–N6 have
not started and full-P4 M3 remains paused.

## Verified state

- Stabilization `770e405` passed the full local gate and
  [CI 36525856029](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36525856029).
  It repairs the producer guard, obsolete generated modules, completion metadata,
  replay/mutation contracts, text hygiene and cache-context completeness.
- All 153 bodied definitions have compiled forward and reverse correspondence
  theorems. Extern-dependent claims assume `externsContract`; print-dependent
  claims assume empty hints. All generated runtime-domain claims compile.
- The completion manifest records 350 declarations, 888 obligations and 758 claim
  bindings. Of 130 unbound items, the CLI checks source identity; 129 remain
  unresolved across stages. Strict bounded N2 passes. N3-owned domain contracts
  still missing: `ite`, `repeat_`, `empty_set`, `empty_map`.
- Performance commits: catalog reuse `2ee52b9`, normalization `c5974e7`, independent
  proof directions `fa522c6`, optional native replay `d28d3b8`. No theorem statement,
  proof body, audit or obligation was removed. No source pin changed.

## Validation and performance

`nix develop -c /usr/bin/time -l -p scripts/check.sh` exited 0 on the combined
implementation: 835.25s wall, certificate/library stage 668s, no skipped stages.
The repaired baseline was 1073.97s / 903s. A warm full gate exited 0 in 118.93s.
All executable inputs are unchanged through `d28d3b8`; subsequent evidence-only
edits reuse these passes with fresh text/link checks and independent review.
Ignored logs are `.artifacts/perf/codex-optimized-gate.log` and
`codex-optimized-warm-gate.log`. Actual native replay and native `--no-build`
replay also exited 0. Final matched saved-proof replay was 288.39s ordinary versus
265.09s native (8.1% faster), both exit 0. Main CI's certificate stage was 2043s
versus 2110s at baseline (3.2% lower). Both restored the same main cache; these
single runs show a smaller Linux gain and do not establish a stable latency.
The remote log is `codex-optimized-ci.log`.
See [performance evidence](notes/proof-build-performance.md)
and the [public snapshot](../docs/performance/n3-iteration-2026-09-28.md).

Independent read-only Codex GPT-6 Astra reviews found no remaining blocker;
implementation and bounded tests used GPT-6 Sol agents. A second Astra reviewer
reviewed the fact-lookup optimization authored by the first. Reviews are AI-agent
reviews, not human review. Full gate execution was owned by the parent agent.

## Next steps

1. Resume the four N3 domain proof shapes using the catalog-backed field resolver.
   `empty_set`/`empty_map` need constant-result domains; `ite` selects an admitted
   input; recursive `repeat_` needs a partial-correctness argument. The earlier
   20-minute recursive representation-planning route is removed from production
   source-domain planning.
2. Regenerate completion, require `--require-owned N3`, update the
   [Nano plan](notes/nano-certification.md), and run the full gate plus independent
   review before declaring N3 complete. Broader stage obligations are not waived.

For tactic iteration, build core once and use `scripts/replay-cert.py` with a
selected theorem/direction; `--native` is optional and `--no-build` rejects stale
native artifacts. Aggregate module names expand to real proof sources. Directly
checking an aggregate file only imports existing proofs. Replay is faithful for
tactic-only changes, not evidence for regenerated or changed dependencies.
Run one build/replay at a time per checkout.

## Repository state

On `main`. After passing integration CI, verified-merged local refs `n3-core`,
`n3-runtime`, `n3-expr-eval`, `n3-perf` and `n3-perf-next` were removed, along with
remote `n3-core` and `n3-perf`; branch listings verified removal. Preserve local
`n3-decl-load` (`82fbe2e`, superseded implementation but not an ancestor) and the
unrelated `docs/repository-review` branch. The old `../p4-spectec-lean-replay`
worktree contains uncommitted experiments that differ from main and is retained.
The expected four-file upstream exporter patch remains applied.
