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

Follow-up review of commit-message guidance and AI disclosure: no blocking
findings. The explicit Beams/Git rules preserve the existing convention
and required coauthor trailer. The PR accurately attributes implementation,
writing and separate AI-agent reviews without implying human review.
Labeled AI disclosure as user-required so the adjacent GitHub/Google
references are not misrepresented as its source.

Final merge/disclosure review: no findings. The per-PR merge policy
preserves meaningful commits by default without bypassing checks or
protections. Per user preference, the PR has no merge-strategy section
and only one disclosure sentence naming agent and verified model.
Review evidence remains explicitly labeled AI-agent review.
