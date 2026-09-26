# Dynamic Nano driver/main reconciliation review

Independent read-only reconciliation review by the corpus agent, 2026-09-25.
Only this report was written; no source, gate, fixture or status edits were made.

## Revision and scope

Reviewed the staged merge of driver checkpoint
`2635a3224f33ea235fb6727399685d3b710018b5` with published main
`d0397865aad2e22945f054e941dea3fdfa11693a` in the isolated Nano driver tree.
This is source-preservation and gate-integration review, not a new semantic
driver audit. The previously filed driver and gate reviews remain the
semantic and narrow-wiring evidence.

## Findings

No reconciliation findings.

- Staged `P4SpecTec/`, Nano target/oracle/packet/driver tests, Nano fixtures
  and library root imports are byte-identical to the driver parent.
- Incoming corpus worker, corpus inventory/contracts/shard files and
  `scripts/export-p4-oracle.py` are byte-identical to the incoming main.
- Source, Lake and gate working files match the staged merge. The staged
  whitespace check passes.
- Lake retains both `p4-corpus-worker` and `check-nano-driver`. The gate
  retains all corpus required files, unconditional 5/7/16 offline suites
  with failure propagation, the worker build and all driver required files
  and checks. No upstream-dependent corpus execution or network fetch is
  introduced into ordinary CI.
- The status reconciliation preserves bounded evidence, prior pilot identity
  limits, merged PR/CI records and outstanding combined driver gate/final
  publication obligations. Canonical corpus launch is not represented as
  completed corpus coverage. The denominator remains 1,352 raw paths,
  eighteen omitted helpers, 67 exclusions and 1,267 candidates.

## Independent checks

All commands ran in the pinned `nix develop` shell in the driver tree.

- `git diff --cached 2635a32 --exit-code -- P4SpecTec` plus the Nano test,
  fixture and root-import paths: exit 0.
- `git diff --cached d039786 --exit-code -- test/p4-corpus
  P4SpecTecTest/Diff/P4Corpus scripts/export-p4-oracle.py`: exit 0.
- Working versus staged source/Lake/gate diff and `git diff --cached --check`:
  exit 0.
- `bash -n scripts/check.sh`: exit 0.
- `python3 test/p4-corpus/test_inventory.py`: five tests, exit 0.
- `python3 test/p4-corpus/test_contract.py`: seven tests, exit 0.
- `python3 test/p4-corpus/test_shard.py`: sixteen tests, exit 0. The printed
  synthetic worker-timeout is an expected fault-injection test.
- `python3 test/nano-target/test_contract.py`: eleven tests, exit 0.

No full local gate or remote CI was run or claimed by this reviewer. Root
owns the live combined full gate and final-head publication requirements.
