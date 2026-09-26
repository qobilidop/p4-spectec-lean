# Direct-commit workflow review

Independent read-only review by `/root/p4_oracle`, 2026-09-26.

Reviewed the bounded workflow changes in `AGENTS.md`, the in-place decisions,
status and the matching design checkpoint sentence. They implement the user's
explicit approval: normal changes go directly to main, branches provide useful
isolation, and PRs are created only on explicit request. Independent review,
the recorded full local pre-push gate, post-push CI and repository protections
remain mandatory. Feature integration preserves coherent history and cleans
up refs/worktrees after successful main CI. Requested PRs retain final-head
review and remote CI before merge.

One finding was resolved: the old unconditional requirement to push unfinished
work on a branch contradicted optional isolation and could imply publishing
failing WIP. Both AGENTS and design now distinguish validated normal commits
from isolated incomplete experiments and prohibit pushes without a passing
gate, documenting local checkpoints when validation blocks publication.

No remaining findings or operative PR-first contradictions found in the
reviewed instructions, decisions or polished design. `git diff --check` in
the pinned Nix shell exited 0. Root's full gate was still running; no fresh
full-gate or remote CI verdict is claimed here. Only this review file was
written; no implementation, ref or other documentation changes by reviewer.
