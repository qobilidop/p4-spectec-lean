# Repository stewardship

Active maintenance checkpoint, 2026-09-26. Retain this note for the current
organization change and its review; compact it after publication, keeping
any unresolved findings. Baseline: `968ad65`.

## Scope and disposition

The user approved a topic-oriented working memory, not a new feature campaign.
Status holds the immediate checkpoint, Decisions cross-cutting rationale,
Roadmap deferred work, and notes topic-specific plans/investigations/reviews.
AGENTS remains the policy owner. The skill is maintained tooling.

- State/runtime notes and reviews become a state-integration topic plus focused
  byte-text, type-runtime, print-hints and encoding notes.
- Full-P4 notes/reviews become an overview, corpus guide and review evidence
  together under `full-p4/`. The checked census remains byte-identical at
  `p4-census.json`; moving it would create unnecessary tooling changes.
- Nano target/driver/verify material becomes `nano-target.md`.
- Completed field-update and library-boundary evidence becomes `field-update.md`.
- The requested certification discussion remains `compiler-certification.md`,
  incorporating still-open design-review judgments. Public research synthesis
  remains in Related Work, not duplicated here.
- The long decision register is divided between concise cross-cutting choices,
  `translation-design.md`, and topic-specific constraints. The obsolete
  blanket M3 authorization is explicitly superseded by the user's pause.
- Archive recovery remains in `archive.md`; no backup, branch or worktree
  is removed in this pass. Completed standalone review reports and empty
  placeholders are removed only after their useful content is preserved.

Original reports, exact command dumps and frozen source identities can be read
with `git show 968ad65:<original-path>`. Former review paths are historical
identifiers, not live links. This is consolidation of evidence, not a new
semantic audit. No ignored logs are required to understand retained obligations.

## Retained completed maintenance evidence

The skill at `968ad65` passed the bundled metadata validator, independent
`tend_repo_review` review and `tend_repo_trial` read-only forward test.
The trial preserved paused work and identified stale state without editing it;
it led to explicit proposal-only validation guidance. PyYAML was supplied
temporarily from locked nixpkgs, with no project dependency change.

The 2026-09-26 direct-commit workflow review by `p4_oracle` resolved the
contradiction between optional branches and compulsory publication of failing
WIP. AGENTS now owns that rule; the obsolete PR-first report is historical.

Documentation reviews by `doc_guides_review` checked Design/Certification
against actual theorem contracts and independently summed the 48-module
860.6-second historical timing table. They did not run a new benchmark.
The final rewrite retained failure/state, representation, environment and
reverse-witness obligations. All 33 public local links/anchors then passed.
Detailed reports remain at `968ad65`; current artifact documentation owns
their conclusions, not this working note.

The earlier archive review by `p4_oracle`, with sequencer inventory by
`state_props`, verified preservation before user-approved deletions.
PR #28 merged as `d503d36`, preserving `acfa45e`; run `36229832016`
passed on that head. Later removal of the 24 GiB snapshot deliberately
discarded ignored artifacts, not committed history. Recovery limits remain
explicit in the archive note.

## Review and validation of this pass

Independent cross-review by `compact_full_p4` covered root-authored entry
points, Nano/field-update/discussion/translation notes, and `compact_state`'s
six topic files against the original notes/reviews at `968ad65`. Findings
retained the original after-M1/at-M4 website schedule, exact unsupported typed
Nano exclusion/propagation rule, and unusual upstream optional-membership
success. These were fixed without changing implementation.

Independent `compact_state` review covered the full-P4 consolidation and
AGENTS/skill diffs. It identified missing reviewer identities; root restored
them in the compact full-P4 evidence. Root identified and source-checked a stale type-runtime
statement: corpus-v2 now has a five-phase tick sentinel, while general
Type.Fresh semantics remain unmodeled. Review confirmed that correction.
Neither writer independently reviewed its own replacements; no new upstream
capture, corpus execution or semantic audit is claimed by these reviews.

This first real skill application motivated two narrow changes: map content
to its owner before moving files, and distinguish maintained data/historical
review evidence from disposable notes. The skill does not prescribe this
repo's folder policy again; AGENTS owns it. The updated metadata validator
passed in the same locked temporary PyYAML environment.

All 87 removed paths were verified recoverable at `968ad65` and absent from
the working tree; the empty review directory is absent. The census is
byte-identical. A read-only link/anchor check covered all 51 local links in
20 Markdown files (AGENTS plus working memory), with no failures. Text,
staged whitespace and file-size checks passed. Full-gate results and
publication state belong in status. Nothing under source, tests, public docs,
pins or build configuration changed.
