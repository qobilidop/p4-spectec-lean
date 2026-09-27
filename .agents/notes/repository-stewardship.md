# Repository stewardship

Current requested maintenance and session handoff, 2026-09-27. Retained for
scope, independent review and publication evidence; compact at the next upkeep.
No implementation work is active and N3 is not authorized by this cleanup.

## Disposition

- Shorten status to the validated N2 checkpoint, future resume point and
  preserved repository state. Distinguish implementation `76bed84` from the
  final closure record `d85e82c`, whose exact-revision CI also passed.
- Consolidate N2 verification and review history in its topic note; remove the
  completed 54-record review collection after retaining provenance, resolved
  findings, limits and historical recovery at
  `d85e82c:.agents/notes/nano-certification-review.json`.
- Preserve all N2 source-domain and composition constraints, the unchanged
  N3–N6 exit criteria, full-P4 pause and all 78 typing/39 STF corpus cases.
  Record the discussed 45–90-hour remaining forecast and 4–8-hour proposed
  first N3 checkpoint, explicitly without new implementation authorization.
- Clarify the old CI optimization note's historical pause and the original
  coverage schema versus current schema 3. README/public certification remain
  accurate; no semantic claims, pins, code, tests or generated data change.
- Preserve the old docs branch, archive backup, single worktree and expected
  upstream exporter patch. The already-removed N2 branch is not recreated.

## Evidence-backed learning

N2's first remote gate found an ignored raw export dependency that a warm local
checkout hid. The committed fix `76bed84` makes inventory fixtures read the
tracked compressed snapshot; all 36 tests passed with the raw export absent.
The corrected full gate and remote CI then passed. This is a concrete fixture
fix and retained validation example, not a reason to add another global rule.
Nominal dictionary/parameter binding choices remain in Decisions and checked
regressions; this cleanup introduces no new policy or skill requirement.

## Earlier upkeep evidence

The code organization (`ad1ac33`) and meaningful ordering (`29ddf22`) passes
remain complete. Their full gates and exact-revision CI passed; independent
Sol/Astra cross-reviews excluded each author's own changes. Generated behavior
and independent oracle comparisons were preserved. Current placement and
ordering policy live in AGENTS/Decisions. Original scoped hashes, findings,
validation and limits are recoverable at the historical Git path
`d85e82c:.agents/notes/repository-stewardship.md`.
The subsequent asynchronous-CI policy is owned by AGENTS, not this note.

## Current review and validation

Luna `maintenance_scan` independently checked Nano public claims and pin/runtime
boundaries; no overclaim found. Its implementation-versus-closure revision
clarification is reflected in the handoff. Sol `organize_lean_tests` inspected
all 54 review records and found no unresolved findings before removal; the
retained constraints and historical recovery are kept in the Nano note.
These are read-only AI-agent checks, not fresh semantic proofs or recaptures.

Independent read-only Sol `organize_lean_tests` review against `d85e82c` found
no lost obligations or remaining findings. N2 requirements and N3–N6 plan
sections remain byte-identical. The reviewer verified committed recovery and
live deletion, source-domain constraints, estimate units and the lack of N3
authorization. Ordered path+NUL+bytes fingerprint of the six changed existing
files (excluding the deleted review collection):
`791abc5636d1ae7d7b6986f5eb72fc690c63efda964a71c4e403e602acb270e2`.
This review record and an optional wording precision ("resolved findings")
were added afterward; no implementation change followed review.

Fresh checks passed with actual exit 0: `scripts/check-text.sh`,
`git diff --cached --check`, and read-only local-link/anchor verification
(39 Markdown files, 111 local targets, 16 Markdown anchors). All 54 original
review records are recoverable at the named Git revision; directory listing
confirmed the deleted file absent. The executable-tree comparison against
`d85e82c`, excluding `.agents` and the expected dirty upstream submodule,
returned exit 0. Lake library/executable ownership and strict `--require-n2`
gate wiring remain unchanged.
This documentation-only pass reuses full local gate 47761 (actual exit 0,
all 44 stages, no skips) for implementation `76bed84`, with unchanged executable
inputs through `d85e82c` and successful
[CI 36316496027](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36316496027).
No full rebuild, Lean test rerun, upstream recapture or corpus campaign is run
for this prose-only maintenance. Routine publication CI is asynchronous.

At the next session, inspect the latest main CI before starting unrelated work.
This maintenance publication may still have its routine CI pending at handoff;
never reuse the earlier implementation pass as a verdict for that new run.
