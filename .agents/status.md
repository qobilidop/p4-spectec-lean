# Status

Current checkpoint, updated 2026-09-26.

## Authorized scope

The user explicitly resumed Nano certification and requested completion of N1.
Its implementation and independent reviews are complete; publication and final
remote verification are active. No N2 expansion has started. Broader full-P4 M3
remains paused. The [Nano plan and evidence](notes/nano-certification.md) owns the
exit criteria, proof limits, review provenance and measured costs.

## Verified N1 checkpoint

- Reviewed local commits: `60f2e72` (optional/negated reverse composition),
  `cc45c7f` (actual print dispatch), `7b4e0b3` (recursive exists_ reverse induction)
  and `591eb60` (actual recursive relation probes).
- This checkpoint adds an explicit runtime-only raw-extern carrier, preserving
  source quotes and packet/object membership. Actual short/full extract probes
  compare generated continuation contexts canonically and fresh counters exactly.
  A kernel-checked paired source/generated receiver-reuse mismatch closes the
  bounded contextual obligation; full target composition remains N4.
- Printing composes through actual builtin dispatch with explicit guard-free,
  empty-hint and environment assumptions. Recursive exists_ reverse execution
  covers all related Boolean lists and every terminating generated outcome;
  it does not claim initialization or total termination. Type_eq/ParameterType_eq
  probes use actual definitions, including recursive success, mismatch and
  exhaustion; universal recursive-group certificates remain N2.
- Independent reviews found no unresolved issue. A coverage-test profile mismatch
  and imprecise context-equality wording were fixed. Reviewers distinguished
  direct-handler hard error from subsequent AL callee mismatch.
- Full local `nix develop -c bash /Users/qobilidop/my/work/p4-spectec-lean/scripts/check.sh`
  passed with actual exit 0 (session 40282, 104.859s), all 44 stages, no skips.
  Evidence: `.artifacts/n1-full-gate.{log,json}`. This includes warning-failing
  libraries/tests/examples, all existing certificates, both typing replay legs,
  packet/verify replay, mutations, generated freshness, coverage, quotations,
  source pin checks and full-P4 census. Final prose updates receive text/link checks.

N0 is complete. N1's proof/representation/observation feasibility work is complete;
final remote CI still gates milestone closure. Coverage remains 350 declarations,
888 obligations, 95 bindings and 793 unresolved: 18 generated forward certificates,
77 relation run-soundness theorems and zero generated reverse certificates.
The handwritten proofs add no completion binding. All 78 typing programs and
39 STF sessions remain in the denominator; only three STF sessions have stored
upstream observations. No new upstream capture or full-P4 campaign was run.

## Prior completed work

Code/test organization, meaningful configuration ordering and the requested
maintenance pass are published and validated; [maintenance evidence](notes/repository-stewardship.md)
retains their reviews. The autonomous build/test/CI optimization pass is complete
through `fd7ff9fd47aea72be1290b87e50be3ac1aa459d6`, whose
[CI 36286394307](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36286394307)
succeeded. The [performance evidence](notes/ci-performance.md) and
[public snapshot](../docs/performance/build-test-ci-2026-09-26.md) preserve the
measurements and limits. Routine CI is asynchronous; milestone closure requires
passing CI for the final published revision, as specified in AGENTS.

## Next step and recovery

Publish the reviewed, locally validated N1 checkpoint, verify its remote CI,
and close N1 with the exact publication evidence. Then N2's next concrete work
is reusable source-domain/representation and primitive contracts, followed by
generated two-way certificates for the original 18 functions, recursive relation
group and Var_init closure. Full Nano certification remains incomplete.

The old unpushed `wip/nano-reverse` draft at
`efd626c7cb40004f8d6725f2b29172d09ecd8dbe` was recovered and completed in
`7b4e0b3`; the [historical handoff](notes/nano-certification.md#n1-recursive-proof-handoff)
records its limits and resolution. Remove the obsolete branch after successful
integration and main CI. Its temporary worktree is already gone.

The expected four-file upstream exporter patch remains applied; no pins changed.
There is one registered worktree. The older `docs/repository-review` branch and
local-only [archive backup](notes/archive.md) are preserved. No agent proof/build
processes remain active.
