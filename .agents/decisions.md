# Decisions

The decisions in force, grouped by topic, each with its reason and the
date it was made. A register, not a diary: a superseded entry is
rewritten in place with the new date and reason; an entry whose subject
no longer exists is removed. A decision the design document already
settles is not repeated here.

## Pins

- **P4-SpecTec is pinned at `2730cfd9`** (2026-09-22, "Merge pull request
  #320 from kaist-plrg/fix-batch-1"), the head of `main` when the project
  started, with green upstream CI. Bumped by moving the submodule and
  re-running the exports and the mirror checks. (2026-09-25)
- **Lean `v4.34.1`, Batteries `v4.34.0`, no Mathlib.** The current stable
  release at project start; Batteries at the matching minor. Bumped
  together. (2026-09-25)

## Process

- **No git tags.** Compaction and archiving rely on git history alone;
  the user does not want tags. (2026-09-25)
- **Small self-contained changes commit directly to `main`;
  multi-commit or build-affecting work gets a branch.** Decided by
  judgment per change, stated in one line when committing. (2026-09-24)
