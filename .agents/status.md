# Status

N3-owned proof milestone closed, 2026-09-29. Implementation `67f67ae` is on
`main` with passing [CI 36538318591](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36538318591).
All four final source-domain certificates compile; the strict inventory reports
zero unresolved core obligations owned through N3. The full local gate passed in
124.00s, with no skips. This evidence-only checkpoint preserves those executable
inputs. No implementation is active. N4–N6 remain planned, full-P4 M3 is paused,
and N4 needs a separately authorized scope.

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

## Checks and review

The four actual generated `NanoP4Spec.Refinement.SourceDomain.*` modules built
with `--wfail`, including axiom audits, exit 0. Initial full gate exited 1 only
because the new renamed-recursion test had a Lean layout error. Its first correction
also failed; the final named-definition form passed the focused test build.
Both strict N3 checks passed with zero unresolved items. The corrected full gate
(`nix develop -c /usr/bin/time -l -p scripts/check.sh`) returned actual exit 0 in
124.00s, no skips. Log: `.artifacts/perf/n3-domain-gate-validated.log`.
Fresh text, whitespace and 36 relative-link target checks passed. Final
independent documentation review required a historical-estimate anchor correction,
now resolved. Main CI for `67f67ae` passed the full gate and upstream pin checks;
its certificate stage took 10s. Log: `.artifacts/perf/n3-domain-ci.log`.

Independent read-only Codex GPT-6 Astra review found a zero-input coverage bug,
required its correction, and re-reviewed all four generated contracts, exact
coverage/completion diffs and stronger gate flags with no remaining semantic
blocker. GPT-6 Sol authored the first three shapes; the parent added repetition,
the zero-input fix and integration. These are AI reviews, not human review.
[The work note](notes/n3-source-domains.md) preserves validation and resume details.

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
Those experiments are unrelated to this checkpoint. The merged local
`n3-source-domains` branch was removed after passing main CI; branch listing
verified removal. The expected four-file upstream
exporter patch remains applied; no source pins changed.
