# Status

Current checkpoint, updated 2026-09-26.

## Authorized scope

The organization refactor, ordering cleanup and requested `tend-repo` pass are
committed and published. Maintenance commit `f6a96f2` passed independent review
and the full local gate (session 41273, exit 0, no skips); its
[CI 36283005578](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36283005578)
succeeded. Asynchronous routine CI is authorized and implemented
in `7ebf4ea`; AGENTS owns the policy. The user additionally approved roughly three
hours of autonomous build/test/CI optimization, through about 2026-09-27 03:41 UTC.
The [performance workstream](notes/ci-performance.md) records measurements,
ownership and checks. Preserve all semantic verification while reducing work.
Nano proof implementation and broader full-P4 M3 remain paused during this work.

## Verified checkpoint

- `ad1ac33`: code/test ownership, shared oracle plumbing and compiler/proof
  responsibility splits. Independent Sol/Astra reviews found no outstanding
  issues. Full local gate exited 0 (session 65742, no skips), and exact-head
  [CI 36280484313](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36280484313)
  succeeded. Generated output, oracle payloads and certification counts stayed
  unchanged; semantic tests and independent replay paths were preserved.
- `29ddf22`: configuration/import ordering by purpose, with alphabetical peers
  and preserved semantic/upstream order. Independent Sol review passed; the
  full local gate exited 0 (session 61425, no skips).
  [CI 36281893597](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36281893597)
  succeeded for `29ddf22fc5dbfb3dc77d7a7a57fbcaa5ab04db2e`.
- [Maintenance evidence](notes/repository-stewardship.md) records refactor review
  provenance, compaction, retained obligations and this pass's checks.
- First performance increment: single ownership of unit/oracle builds and 44
  timed gate stages. Independent cross-review passed; full local gate session
  21389 exited 0 with no skips. Census/proof optimization remains in progress.

The [Nano plan and evidence](notes/nano-certification.md) owns N0/N1 details.
N0 is complete; N1 is incomplete. Current coverage: 350 declarations,
888 obligations, 95 bindings and 793 unresolved; 18 forward certificates,
77 relation run-soundness theorems and no generated reverse certificates.
All 78 typing programs and 39 STF sessions remain in the denominator. The
latest full gate passed both typing differential legs; only three STF sessions
have stored upstream observations. No full-P4 campaign was run.

The combined N0/reverse-foundation checkpoint `f6d1b05` (including `35bda29`)
passed exact-head CI 36276724234; target/printing probes `9309e26` passed
exact-head CI 36277488013. Source and
representation coverage, primitive contracts, initialization, target composition
and corpus completion remain open. The bounded field-update consumer and
[coverage machinery](notes/coverage.md) are complete, not the Nano milestone.

## Next step and recovery

Finish reviewed, measured performance improvements within the authorized window;
inspect latest main CI at each checkpoint and prioritize any failure. The next
Nano feature step, after this optimization work, is the actual `exists_` reverse induction
on local unpushed branch `wip/nano-reverse` at
`efd626c7cb40004f8d6725f2b29172d09ecd8dbe`. Its historical
`.agents/notes/nano-reverse-proof/README.md` distinguishes checked clauses from
the unverified full draft. The [handoff](notes/nano-certification.md#n1-recursive-proof-handoff)
records hashes, review limits, cost and remaining outcome/fuel composition.
The branch has no passing full gate and must not be published as complete;
its temporary worktree is gone. Preserve main's status when recovering it.

Then exercise `Type_eq`/`ParameterType_eq` and prove a faithful raw-extern
representation contract. Extract's raw result cannot be represented by the
current generated value type; no replacement has been adopted. Empty-hint
printing has a checked generic theorem but still needs builtin/environment
composition. Bounded internal-fuel probes are not a general safety proof.
N1's full exit criteria still block broad proof generation.

The expected four-file upstream exporter patch remains applied; no pins changed.
There is one registered worktree. The older `docs/repository-review` branch and
local-only [archive backup](notes/archive.md) are preserved, as is the unpushed
Nano WIP. No proof-attempt verification processes remain.
