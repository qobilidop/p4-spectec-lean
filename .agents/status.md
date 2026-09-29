# Status

Autonomous performance work, checkpoint 2026-09-28. Implementation through
`d28d3b8` on `n3-perf-next` has independent review and passing full local gates;
final integration and remote CI remain before closing this task. Published N3
history is preserved. N0/N1/N2 are complete; N3 remains incomplete. N4–N6 have
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
replay also exited 0. See [performance evidence](notes/proof-build-performance.md)
and the [public snapshot](../docs/performance/n3-iteration-2026-09-28.md).

Independent read-only Codex GPT-6 Astra reviews found no remaining blocker;
implementation and bounded tests used GPT-6 Sol agents. A second Astra reviewer
reviewed the fact-lookup optimization authored by the first. Reviews are AI-agent
reviews, not human review. Full gate execution was owned by the parent agent.

## Next steps

1. Integrate the reviewed performance checkpoint into `main` without rewriting
   published history. Require passing remote CI for the final revision, then
   clean up integrated feature refs and the disposable replay worktree.
2. Resume the four N3 domain proof shapes using the catalog-backed field resolver.
   `empty_set`/`empty_map` need constant-result domains; `ite` selects an admitted
   input; recursive `repeat_` needs a partial-correctness argument. The earlier
   20-minute recursive representation-planning route is removed from production
   source-domain planning.
3. Regenerate completion, require `--require-owned N3`, update the
   [Nano plan](notes/nano-certification.md), and run the full gate plus independent
   review before declaring N3 complete. Broader stage obligations are not waived.

For tactic iteration, build core once and use `scripts/replay-cert.py` with a
selected theorem/direction; `--native` is optional and `--no-build` rejects stale
native artifacts. Aggregate module names expand to real proof sources. Directly
checking an aggregate file only imports existing proofs. Replay is faithful for
tactic-only changes, not evidence for regenerated or changed dependencies.
Run one build/replay at a time per checkout.

## Repository state

The worktree is on `n3-perf-next` pending final integration; `n3-perf` contains the
passing stabilization checkpoint and includes `n3-core`. Other integrated/superseded
feature refs remain until final main CI. `../p4-spectec-lean-replay` is the old
scratch worktree. The expected four-file upstream exporter patch remains applied.
