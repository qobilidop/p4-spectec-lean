# Repository stewardship

Durable, 2026-09-29. Retained as the evidence index for requested repository
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
  GPT-6 Astra review in the later Codex pass (`aa5865f`) checked the compaction
  and found no lost obligations; this does not supply review at publication.

- Shared skill source gate (`aa5865f`, Codex tend-repo pass): the layout gate
  now requires `.claude/skills` to be a symlink resolving to `.agents/skills/`
  (`-L` and `-ef`), beyond the skill existing. Six focused link scenarios and
  full gate session 47002 returned actual exit 0; an independent GPT-6 Astra
  read-only review found no blockers (reviewed `scripts/check.sh` SHA-256
  `2f1ca940dc670d514a152069d5226cf87e222fe253b771fb97dc23e104f34eae`; it did not
  rerun the cases or gate).
  [CI 36341571853](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36341571853)
  passed. Full record at `aa5865f:.agents/notes/repository-stewardship.md`.

- N3 handoff compaction (`ffc21e7`, Claude Code) condensed completed N2 evidence,
  recorded then-open N3 blockers, corrected counts and rebased two local WIP refs.
  It reused `b6f1576`'s actual exit-0 full gate (45 stages, no skips) and passing
  exact-revision CI 36357022016; fresh text/whitespace/link checks passed.
  Independent-context Claude Opus review resolved scope/evidence wording and
  found no remaining blocker; it ran no builds and did not review blocker
  semantics beyond commit messages. This is AI review, not human review.
  The original record and historical WIP identities are recoverable at
  `ffc21e7:.agents/notes/repository-stewardship.md`. Current refs belong in status;
  this historical record did not establish a CI outcome for `ffc21e7` itself.

- N3 closure maintenance (`fde887c`, on `6ca3a22`): documentation only,
  consolidating the source-domain note into the Nano plan; reused `67f67ae`'s exit-0
  full gate (124.00s) with fresh text, whitespace, boundary and 120-link checks;
  independent Codex GPT-6 Astra review found no blockers (reviewed diff SHA-256
  `f6a08fdafdfc3889abc44ccc6a61354558463c7747499afd5ce71f6b0faf567f`); AI review, not
  human review, and the reviewer ran no builds. Its exact CI 36543103039 passed. Full record at
  `bd7ed63:.agents/notes/repository-stewardship.md`.
- Post-N4 pass (2026-09-29), based on `bd7ed63`: CI 36603339319 passed (freshly
  queried). Documentation and working state only: compacted the Nano plan to closed
  stage evidence, binding constraints and the N5/N6 plans (detailed N2/N3 narrative
  recoverable at `bd7ed63:.agents/notes/nano-certification.md`); shortened the roadmap
  milestone paragraph and corrected N1's implementation versus closure commits; repaired
  two anchors to removed headings; corrected the target oracle README, which still
  denied payload normalization; added the two N4 checks to the AGENTS command list;
  added four N4 traps to the Lean pitfalls. No pins, generated artifacts, code, branches
  or worktrees changed. Validation and review are recorded in the commit and status.

## Current maintenance pass

Requested general maintenance after the Nano-P4 milestone closed, based on `bd8be30` (release
`42ffad6`, CI 36697907550 passed; `bd8be30`'s own CI 36699254071 was still running when this
pass began). Compacted the closed N5/N6 plan sections to the constraints that still bind
(plans recoverable at `bd8be30:.agents/notes/nano-certification.md`); rewrote stale
milestone, authorization and gate wording in status, decisions, roadmap, AGENTS and two
notes; added the Nano follow-ups to the roadmap as unauthorized candidates. One executable
change: the gate removes the ignored extracted exports at its start (lesson below). No pins,
generated artifacts, Lean code, branches or worktrees changed. The release record now
describes `42ffad6`'s tree only, so review and release are pending on later trees, by design.
The evidence commit `bd8be30` then failed CI 36699254071: CI checks out shallowly, so the
recorded commit `42ffad6` was absent and the checker raised instead of counting nothing. The
checker now reports such a record as unverifiable in that clone (counting nothing); the
release itself stands on its recorded local strict check and `42ffad6`'s CI. Validation is
recorded in status. Independent Claude
Opus 5.5 subagent review (read-only, no builds) found no blockers; its two should-fix
findings (a status claim contradicted by this change, and stale plan wording in the roadmap
and AGENTS) and the gate-comment, wording and duplication nits are resolved; the
`spec-snapshot.py` docstring nit is left, since the extracted cache is always rebuildable.
The resolution review's N0 claim, direction and scope nits are resolved. A separate independent
review of the shallow-clone fix (Claude Opus 5.5 subagent, read-only) found no blockers; its
findings (a malformed revision excused as absent, constant-mock tests) were resolved: only a
missing object is excused, malformed or non-commit revisions raise, release fields are checked
first, and a real-Git test covers each case. Its confirmation found no unresolved findings.
Two earlier reviewer runs stalled while the machine slept; they reported nothing.

## Shared-skill layout reproduction

The shared-skill layout cases can be reproduced from the repository's Nix shell;
the temporary fixtures are outside the checkout, and the tested block comes
from the gate:

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
- Skill discovery and shared-source identity are distinct checks; the layout
  gate covers both (`aa5865f`).
- N3 iteration was dominated by rebuild latency after tactic changes; the fix
  is tooling (`scripts/replay-cert.py`) and a Lean pitfall entry, not policy.
- N4 twice reached the full gate with defects a cheaper check would have caught: a new
  untracked file escaped `check-text` (which lints tracked files; `git add -N` first),
  and a hand-written axiom expectation (now a Lean pitfall). Both were caught by the gate
  before publication; no new rule, since the gate is the intended backstop.
- The same warm-export trap recurred at N6: release CI for `a65c265` failed because a
  contract stage read the extracted export before the gate extracts it (`42ffad6`). A second
  recurrence justified a mechanism rather than a rule: the gate now removes the ignored
  extracted exports at its start, so local gates fail the same way CI does (2026-09-30
  maintenance pass, above).
