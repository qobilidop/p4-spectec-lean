# Repository stewardship

Durable, 2026-09-27. Retained as the evidence index for requested repository
maintenance passes: what each changed, how it was reviewed and validated, and
where its full record is recoverable. Policy lives in AGENTS, not here. Rewrite
this note at each upkeep; do not append a journal.

## Completed passes

All passes below are published on `main`, with passing exact-revision CI
unless stated otherwise. Historical Git paths are recovery pointers, not links.

- Code organization (`ad1ac33`), meaningful ordering (`29ddf22`) and the
  follow-up tend-repo pass (`f6a96f2`, full gate session 41273): full gates
  and exact-revision CI passed; independent Sol/Astra cross-reviews excluded
  each author's own changes. The documentation-only asynchronous-CI policy
  follow-up (`7ebf4ea`) reused gate 41273 and has no CI run of its own; later
  runs cover its tree. Full record at
  `d85e82c:.agents/notes/repository-stewardship.md`.
- N2 handoff compaction (`8b280a8`): documentation and working state only,
  reusing full local gate 47761 (run on `76bed84`; executable inputs
  unchanged since);
  [CI 36333408622](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36333408622)
  passed. It removed the 54-record N2 review collection, recoverable at
  `d85e82c:.agents/notes/nano-certification-review.json`; its retained
  constraints live in the [Nano plan](nano-certification.md). Luna checked
  public claims and pins (no overclaim); Sol checked the 54 records (none
  unresolved) and the final diff (no lost obligation). These were read-only
  AI-agent checks, not fresh semantic proofs or recaptures. Full record at
  `8b280a8:.agents/notes/repository-stewardship.md`.
- Agent parity (`d9be55f`), scoped by the user to Claude Code and Codex,
  with other agents configured only once adopted (a drafted Gemini CLI config
  and wider ban list were dropped). Both load `AGENTS.md`, but
  headless probes showed only Codex discovering `.agents/skills/`. The
  `.claude/skills` symlink fixed that, verified by a fresh Claude Code probe
  and by loading `tend-repo` through it; the gate requires the link to
  resolve. AGENTS gained vendor-neutral model tiers, the exact trailer rule,
  the review gate for agents without subagents, a Claude disclosure example
  and the 32 KiB Codex limit. Two read-only Claude subagent reviews, run on
  the same model as the author (independent context, not independent
  vendor): the first found a
  review-gate weakening, an unenforced ban list, an abbreviated trailer
  example and layout nits, all fixed; the second found no blockers. Full
  local gate: actual exit 0, all 44 stages, no skips;
  [CI 36340173018](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36340173018)
  passed. Full record at
  `d9be55f:.agents/notes/repository-stewardship.md`.

## Retained lessons and follow-ups

- N2's first remote gate exposed an ignored raw-export dependency hidden by a
  warm checkout; `76bed84` made fixtures read the tracked snapshot. A
  concrete fixture fix, not a new global rule.
- A Claude Code skill is discovered only under `.claude/skills/`; Codex reads
  `.agents/skills/`. Recorded in AGENTS and gated.
- Deferred, optional: a gate check that `.claude/skills` is a symlink rather
  than a copy. Adopt if a copy ever appears.
