# Corpus inventory/v2 gate wiring review

Independent reviewer: Codex state_codegen agent, 2026-09-25. Read-only code
review of the staged gate-plumbing change over
`e31c1e8da898a2a3ec6a840f0a6a148ca53a8a6c`; reviewed `scripts/check.sh`
blob `928e81e856078bd1eed8a12263b0c4b50a9be05c`. This report does not replace
root's separate inventory, worker, oracle or real-pilot reviews.

No findings.

- All nine new corpus paths are required by the existing missing-file loop,
  including the worker, documentation, committed manifest, probe, driver,
  contract and both offline suites. Missing paths set the gate failure flag.
- Five inventory tests and seven v2 contract tests run unconditionally,
  before the Lean availability branch. Each nonzero result sets `fail=1`,
  and the existing final check exits nonzero. No new skip path was added.
- The tests inspect the committed manifest and synthetic fixtures; subprocess
  sensitivities launch only bounded local Python children. Real upstream,
  p4c/probe initialization and worker execution are mocked where exercised.
  Imports do not invoke the real pilot. The ordinary gate does not fetch p4c,
  compile OCaml, access the network or run a corpus shard through this wiring.
- `p4-corpus-worker` is added to the existing explicit `lake build --wfail`
  tool list, with failure propagation unchanged. Its Lake executable root
  is exactly `P4SpecTecTest.Diff.P4Corpus.Main`; existing build/check targets
  are retained.

Independent commands, each run through
`nix develop /Users/qobilidop/my/work/p4-spectec-lean --command`, with the
corpus worktree as working directory:

- `bash -n /Users/qobilidop/my/work/p4-spectec-lean-p4-corpus-replay/scripts/check.sh`:
  exit 0.
- `python3 /Users/qobilidop/my/work/p4-spectec-lean-p4-corpus-replay/test/p4-corpus/test_inventory.py`:
  exit 0, five tests.
- `python3 /Users/qobilidop/my/work/p4-spectec-lean-p4-corpus-replay/test/p4-corpus/test_contract.py`:
  exit 0, seven tests.

The full frozen gate and final remote CI remain the publication owner's
obligations. This scoped review did not run a real pilot or corpus shard and
does not establish corpus coverage.
