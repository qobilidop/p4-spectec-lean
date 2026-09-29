# Status

N3-owned proof milestone closed, 2026-09-29. Implementation `67f67ae` and final
evidence checkpoint `6ca3a22` are on `main`; exact final
[CI 36539336394](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36539336394)
passed (rechecked during maintenance). No implementation is active. N4–N6 remain
planned, full-P4 M3 is paused, and N4 needs a separately authorized scope.

## Verified state

- All 153 bodied definitions have compiled forward and reverse correspondence;
  all 77 relations have run-soundness. Extern-dependent claims assume
  `externsContract`; print-dependent claims assume empty hints. Evaluation-domain
  claims use the explicit runtime-inclusive profile where required.
- Source-domain contracts now also cover `empty_set`, `empty_map`, `ite`, and
  `repeat_`. Arbitrary legal parameter codecs and independent admission predicates
  remain explicit; repetition proves successful-output preservation, not totality.
- The completion inventory has 350 declarations, 888 obligations and 762 compiled
  bindings. Of 126 unbound items, the CLI checks source identity; 125 remain across
  stages, including 78 N4-owned core corpus items. Full core/Nano acceptance is
  therefore still incomplete even when owned-through-N3 checks pass.
- The normal gate now requires `--require-n2 --require-owned N3`, retaining bounded
  N2 checks and rejecting regressions in N0–N3-owned core evidence.

## Validation and maintenance

The full local `scripts/check.sh` for `67f67ae` returned actual exit 0 in 124.00s,
no skips. [The Nano plan](notes/nano-certification.md#n3-proof-closure-complete)
preserves targeted checks, resolved failures, independent AI review and exact CI
evidence. This documentation-only maintenance reuses that gate because executable
inputs are unchanged; it does not re-prove semantics or rerun the full gate.
The [maintenance record](notes/repository-stewardship.md#current-maintenance-pass)
owns this pass's fresh checks, review and publication state.

## Next steps

The next separately scoped work is target contracts/composition and complete
corpus evidence, per the [Nano plan](notes/nano-certification.md#n4-discharge-target-contracts-and-compose-packet-execution).
Read that section and `notes/nano-target.md` before choosing the first bounded N4
step. Retain all 78 N4-owned core corpus obligations; metadata binding alone does
not discharge replay. Do not describe N3-owned closure as full core acceptance.

## Performance and repository state

The preceding performance work is complete: local full gate 1073.97s → 835.25s,
proof stage 903s → 668s, warm full gate 118.93s, matched native replay 8.1% faster.
[Measurements and limits](../docs/performance/n3-iteration-2026-09-28.md) retain the
smaller observed Linux gain. Source-domain-only changes avoid the heavy execution
proof dependencies. For tactic-only iteration use `scripts/replay-cert.py`;
new statements/support require real target builds. One build per checkout.

Preserve local `n3-decl-load` (`82fbe2e`, non-ancestor WIP), unrelated
`docs/repository-review`, and the dirty old `../p4-spectec-lean-replay` worktree.
Those experiments are unrelated to this checkpoint. The expected four-file
upstream exporter patch remains applied; no source pins changed.
