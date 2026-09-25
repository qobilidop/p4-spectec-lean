# PR workflow and writing review

2026-09-25, independent read-only reviewer `review_census`.

The PR-default policy, narrow maintenance exception, independent review,
local pre-push gate, remote CI before merge and existing protection
requirements are consistent. Initial review found a stale direct-main
rule in `docs/design.md`; replaced with a reference to `AGENTS.md`.
Stale branch-delivery prose in status was corrected too.

Final review found no blocking issues. PR-writing rules are proportional
and the proposed description accurately distinguishes census probes from
full-P4 support, records the quotation bug and storage tradeoffs, and
separates local evidence from remote CI. Corrected the review-order path
to `P4SpecTec/Codegen/Emit.lean`. Publishing the description remains gated
on the final local validation result, recorded in status.
