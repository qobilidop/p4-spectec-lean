# Nano/main reconciliation review

Independent review of root's reconciliation, 2026-09-25. Parents are the
reviewed Nano checkpoint `96078a04a041d316c7152c49959e151985180794`
and published main `2c85f1bcb491fdf229a06eb1460691799a0d8a8b`.
No remaining reconciliation finding.

The Nano target modules, fixtures, replay executables and library imports
are byte-identical in the staged merge to the Nano parent. The corpus
worker, inventory, manifest, probe, harness and tests are byte-identical
to the main parent. The working tree matches the staged source snapshot.
The automatic Lake merge adds the corpus worker while preserving both
Nano executables. The decisions merge preserves the bounded dynamic target
decision and adds the independently reviewed corpus denominator decision.

The manually resolved gate retains the union of required files and offline
tests, builds the corpus worker plus both Nano executables under `--wfail`,
and still runs the direct and packet-relation Nano checks unconditionally
when Lean is available. It introduces no real corpus execution, p4c fetch,
upstream build, exclusion-based success, or new skip. Status retains the
bounded target limitations and records the incoming published corpus
checkpoint rather than claiming either milestone is complete.

Independent commands in the pinned default shell, from this worktree:

- `git diff --cached --exit-code 96078a0 --` followed by the complete Nano
  implementation/test paths and both library roots: exit 0.
- `git diff --cached --exit-code 2c85f1b --
  P4SpecTecTest/Diff/P4Corpus/Main.lean test/p4-corpus`: exit 0.
- `git diff --exit-code`: exit 0 (working source equals staged source).
- `bash -n scripts/check.sh`: exit 0.
- `python3 test/nano-target/test_contract.py`: exit 0, ten tests.
- `python3 test/p4-corpus/test_inventory.py`: exit 0, five tests.
- `python3 test/p4-corpus/test_contract.py`: exit 0, seven tests.
- `git diff --cached --check`: exit 0.
- Conflict-marker search of `scripts/check.sh` and `.agents/status.md`
  returned no matches (the expected grep exit 1).

These checks ran as one fail-fast focused process (exit 0), apart from the
explicit conflict-marker search. The root agent owns the frozen full gate;
this reviewer did not duplicate it. A preliminary gate attempt coincided
with the in-progress merge and exited 2 on unresolved markers, before the
root's final resolution; it is not a passing gate or evidence about the
resolved snapshot. Full-gate success and final-head remote CI remain
separate publication requirements.
