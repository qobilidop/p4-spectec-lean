# Independent replay gate integration review

2026-09-25, read-only AI-agent review of the `scripts/check.sh` diff against
HEAD in the replay publication worktree. No implementation edits.

No findings. The three replay paths are required by the existing layout
check. The six offline contract tests run unconditionally and propagate
failure to the gate verdict. The interpreter executable joins the existing
`lake build --wfail` invocation and shares its failure handling. This does
not invoke the real OCaml oracle, download inputs or run full-P4 replay in
the ordinary gate. The reviewed test file uses local fixtures and mocks.

The replay executable, driver, offline tests and Lake configuration are
byte-identical to `5657373` (`git diff 5657373 --` those four paths produced
no diff, exit 0). This is a gate-integration review, not a new independent
semantic review of that earlier source or a claim of end-to-end replay.

Independently run from the replay publication worktree, each exit 0:

```sh
nix develop /Users/qobilidop/my/work/p4-spectec-lean --command python3 /Users/qobilidop/my/work/p4-spectec-lean-replay-publish/test/p4-oracle/test_replay_contract.py
nix develop /Users/qobilidop/my/work/p4-spectec-lean --command bash -n /Users/qobilidop/my/work/p4-spectec-lean-replay-publish/scripts/check.sh
```

The first command ran six tests. The final frozen full gate and remote CI
remain the publication owner's validation obligations.

## Main reconciliation evidence

The original publication `94fd99e` passed its frozen full local gate and
remote Gate `36209104840` (4m53s). After PR #19 merged as `c974c3d`, root
independently reviewed the status-only conflict resolution with no findings.
Replay executable, driver, offline tests, Lake configuration and gate script
remain byte-identical to `94fd99e`; no implementation changes were made.
The reconciling agent observed the repeated frozen full local gate exit 0
without skips, including twelve oracle and six replay offline tests. The
exact command is recorded in `.agents/notes/full-p4-interp-replay.md`.
Final merged-head remote CI remains owed; real upstream replay was not
repeated for this source-unchanged merge.
