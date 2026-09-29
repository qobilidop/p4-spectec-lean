# Status

N3-owned proof milestone closed, 2026-09-29. Implementation `67f67ae` and final
evidence checkpoint `6ca3a22` are on `main`; exact final
[CI 36539336394](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36539336394)
passed (rechecked during maintenance). The bounded raw-receiver theorem promotion
has passed local validation and review. No implementation is active; broader N4–N6
implementation and full-P4 M3 remain paused.

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

The new reusable contract and its consuming test passed their focused `--wfail`
build. The full local `scripts/check.sh` returned actual exit 0 in 161.97s, no skips,
including unchanged strict N3 inventory, oracle replay and mutation checks.
Independent read-only AI review found no code issue. The
[Nano plan](notes/nano-certification.md#n3-proof-closure-complete) retains earlier
N3 milestone evidence; this bounded helper does not close an N4 inventory item.
The [maintenance record](notes/repository-stewardship.md#current-maintenance-pass)
owns that earlier maintenance pass's checks. Current contract validation belongs in
the [target note](notes/nano-target.md#reusable-raw-receiver-contract).

## Next steps

The next separately scoped work is target contracts/composition and complete
corpus evidence, per the [Nano plan](notes/nano-certification.md#n4-discharge-target-contracts-and-compose-packet-execution).
The authorized readiness pass selected [short-packet extract and raw-receiver
rejection](notes/nano-target.md#first-bounded-n4-task-extract-without-callbacks)
as the first proposed helper contract, with exact files, missing proof pieces and
acceptance commands. The existing rejection theorem is now in reusable support;
the short-packet proof remains the next separately scoped task. Retain all 78 N4-owned core
corpus obligations; metadata binding alone does
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
