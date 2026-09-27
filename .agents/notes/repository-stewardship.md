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
- Stewardship compaction (`777977f`) retained the evidence index, corrected
  note lifecycle labels and shortened status; executable inputs were unchanged
  from `d9be55f`. Its commit records fresh text, whitespace and link checks;
  [CI 36340498357](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36340498357)
  passed. The committed record does not identify an independent reviewer for
  that compaction; do not infer one from its passing checks. The independent
  GPT-6 Astra review in the current pass subsequently checked the compaction
  and found no lost obligations; this does not supply review at publication.

## Current Codex tend-repo pass

Requested scope: exercise the shared maintenance procedure and refine agent
infrastructure where evidence supports it. Base: `777977f`; its exact-revision
CI above was checked before editing. The hidden working-state inventory and
resume documents remain compact and preserve the paused work, so no files
were moved or removed. This run found no demonstrated weakness in the skill;
its instructions remain unchanged.

The layout gate checked only that the Claude-discovered skill existed, which
also admitted a copied skills directory or a symlink to a divergent copy.
The existing AGENTS rule requires a symlink to the shared `.agents/skills/`.
Enforce both link type and destination identity (`-L` and `-ef`), retaining the
existing skill-existence check. This adopts the earlier deferred review
suggestion in the requested infrastructure pass, without claiming a copy had
appeared in the repository. No new policy or semantic behavior is introduced.

Focused validation returned actual exit 0: `bash -n scripts/check.sh` and
six temporary-directory scenarios executing the exact added gate block.
Relative and absolute links to the shared directory passed; missing links,
copied directories, links to another directory and broken links failed as
expected. Full `nix develop -c scripts/check.sh` returned actual exit 0
(session 47002), with no skip setting. Text hygiene and `git diff --check`
also passed after the evidence edits.
Independent read-only review: a separate GPT-6 Astra context reviewed the
uncommitted diff against `777977f` and found no blockers. It confirmed the
`-L`/`-ef` check, working-note accuracy, unchanged-skill rationale and preserved
worktree, documentation branch and upstream patch. Reviewed `scripts/check.sh`
SHA-256: `2f1ca940dc670d514a152069d5226cf87e222fe253b771fb97dc23e104f34eae`.
The reviewer did not rerun the six cases, full gate, discovery probes or
semantic tests; validation above belongs to the implementation agent. Its
request to retain the focused harness reproducibly is addressed below.
These are AI-agent reviews, not human review. Publication remains pending.

Reproduce the six focused cases from the repository's Nix shell; the temporary
fixtures are outside the checkout, and the tested block comes from the gate:

```bash
set -euo pipefail
repo=$(git rev-parse --show-toplevel)
block=$(sed -n '/^# Both agents must discover/,/^fi/p' "$repo/scripts/check.sh")
root=$(mktemp -d /tmp/p4-agent-layout.XXXXXX)
mkdir -p "$root/.agents/skills" "$root/.claude"
say() { :; }
check() { fail=0; eval "$block"; test "$fail" -eq "$1"; }
check 1 # missing
ln -s ../.agents/skills "$root/.claude/skills"
check 0 # relative link
mv "$root/.claude/skills" "$root/.claude/relative-link"
ln -s "$root/.agents/skills" "$root/.claude/skills"
check 0 # absolute link
mv "$root/.claude/skills" "$root/.claude/absolute-link"
mkdir "$root/.claude/skills"
check 1 # copied directory
mv "$root/.claude/skills" "$root/.claude/copy"
ln -s copy "$root/.claude/skills"
check 1 # wrong target
mv "$root/.claude/skills" "$root/.claude/wrong-target-link"
ln -s absent "$root/.claude/skills"
check 1 # broken link
printf 'All six cases passed; fixtures remain at %s\n' "$root"
```

## Retained lessons and follow-ups

- N2's first remote gate exposed an ignored raw-export dependency hidden by a
  warm checkout; `76bed84` made fixtures read the tracked snapshot. A
  concrete fixture fix, not a new global rule.
- A Claude Code skill is discovered only under `.claude/skills/`; Codex reads
  `.agents/skills/`. Recorded in AGENTS and gated.
- Skill discovery and shared-source identity are distinct checks: the
  current pass strengthens the existing layout gate to cover both.
