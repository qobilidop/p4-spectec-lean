# Full-P4 retained review evidence

Compacted 2026-09-26 from independent read-only AI-agent/root reports dated
2026-09-25. This is historical evidence, not a new semantic review or gate
run. No remaining findings were recorded within the bounded reviewed scopes.
All original reports remain at `968ad65:.agents/reviews/<name>.md`.

Named reviewers: `review_export` authored `m3a-export`, `review_census`
authored `m3a-census`, and `review_quotes` authored `m3a-quotation`.
The state/target agent authored `m3c-corpus-shards-recovery` and then its
hardlink fix, so post-fix checks there are author evidence. The separate
hardlink review covers that fix independently. `m3c-shards-nano-reconcile`
records Codex GPT-6 Sol as reviewer. “Root” below denotes the historical
coordinator, not the author of this compaction.
The executable-codegen agent reviewed `m3c-p4-oracle-adapter`.
Codex `state_codegen` reviewed `m3c-corpus-gate` from `e31c1e8`, gate blob
`928e81e856078bd1eed8a12263b0c4b50a9be05c`.
Codex GPT-6 Sol reviewed the `state_props` hardlink fix in
`m3c-probe-workspace-hardlinks`, excluding its own earlier workspace-key option.

| Original report(s) | Findings resolved and evidence retained |
|---|---|
| `m3a-export` | Sorted upstream traversal/all 108 regions verified; two independent exports byte-matched Nano and P4. Snapshot corruption/truncation/checksum failures preserve cache and stop gate; size guard tests passed. No quotation/full gate review. |
| `m3a-census` | Raw recursion distinguished from emitter mutual blocks; 15 aliases in six groups corrected. Census `--check` passed; counts independently matched. First-error/text-only qualifications required; no full-P4 build. |
| `m3a-quotation` | Gate must execute checker, not only build it. Type/callable namespace fix and all 342 Nano quotations plus QuoteChecks passed. No full-P4 quotation/census/full-gate claim. |
| `m3c-corpus-prep` | Corrected empty-submodule parent-HEAD confusion, exact p4c pin, independent relation sessions and pinned config/symlink/error checks. Root reran ten restore tests and real idempotence (1,352 paths), not initial network fetch. |
| `m3c-p4-oracle-adapter` | Four medium findings fixed at `997d0ab`: stale/dirty linked-source provenance, semantic-text normalization, fail-open manifests/envelopes and crashes accepted as negatives. Independent twelve tests and four cases/eight CLI checks passed. v1 envelope check is not recursive IL typing; later Lean decode is separate. |
| `m3c-p4-interpreter-replay` | At `a4c907b`/`5657373`, corrected syntax-envelope bypass and wrapping counter seeds. Independent six real matches, syntax-only case, nine specific Lean mutation rejections and six offline tests passed. Placeholder externs audited; no packet/generated/corpus claim. |
| `m3c-replay-gate` | Required paths/offline tests/build failure propagation reviewed; six tests and shell syntax passed. Integration preserved `5657373` source; real upstream replay not rerun for unchanged merge. |
| `m3c-corpus-inventory` | Independently reproduced canonical 1,267 candidates, eighteen omitted helpers, 67 exclusions. Five tests including thirteen corruptions and fresh exact-pin inventory passed. No execution/resume claim. |
| `m3c-corpus-worker` | Worker initialization moved inside durable reporting lifecycle. Root independently passed seven tests and full v2 pilot `98530`: six AL matches, syntax-only case, eight CLI checks, sixteen mutations and subsequent valid replay. No shard/full gate claim. |
| `m3c-corpus-gate` | Nine required paths, five/seven unconditional offline tests and worker build propagate failure. Independent tests/syntax passed; no fetch/network/real pilot introduced. |
| `m3c-corpus-shards` | Root reviewed exact identity, terminal/recovery accounting, artifact-first quarantine, final-worker failure and null byte metrics. Sixteen tests and final-helper exact resume `901d53d9` independently passed. No full corpus/generated leg claim. |
| `m3c-corpus-shards-recovery` | Reviewer found hardlink cache overwrite risk, then authored fix; its post-fix tests were author evidence. Original independent fourteen-test recovery review found no other issue. Exception/state-transition injection is not a power-cut test. |
| `m3c-probe-workspace-hardlinks` | Separately authored fix independently reviewed on helper blob `fbabd5fabe16ffcf77729f2d604e4ee3229f81eb`, tests `045382787a6456b481114df1486b0de28a4e2735`; sixteen/seven/twelve tests passed. Reviewer authored earlier workspace-key option, so independence covers only this safety follow-up. Cooperative locks only; no real shard/full gate/CI. |
| `m3c-shards-nano-reconcile` | Shard source unchanged from `2fbe024`, Nano source unchanged from `186d43a`; combined wiring and sixteen/ten offline tests passed. Lake changed hashed identity: earlier `901d53d9` cannot resume as this revision. Reviewer later inspected root's recorded gate exit 0/no skips, without rerunning it. |

The full local gates recorded for oracle publication, replay integration,
worker integration, final shard helper and shard/Nano reconciliation exited
0 without skips. This does not revalidate the present tree. Known historical
remote Gate evidence includes oracle run `36205678753` (1m52s), replay
`36209104840` on `94fd99e` (4m53s), and PR #22 `36213412457` on `93a2e8c`
(3m43s). Original reports explicitly left subsequent merged-head CI to the
publication owner; these reviews alone do not establish those later outcomes.
Current publication state belongs in status and must be checked separately.

The retained engineering constraints from these reviews live in
[corpus](corpus.md) and [overview](overview.md). Historical ignored logs,
temporary review scripts and secondary-worktree observations are not assumed
recoverable; committed source/report history is. None of these checks closes
the failed aggregate casting proof, full denominator, generated replay,
guarded type-fresh semantics, targets or all-definition certification.
