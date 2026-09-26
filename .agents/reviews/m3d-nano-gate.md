# Independent Nano target gate review

2026-09-25, read-only AI-agent review by Codex (GPT-6 Sol). Scope is gate
and fixture/offline replay wiring, not target/interpreter semantic fidelity.
Worktree: `/Users/qobilidop/my/work/p4-spectec-lean-nano-target`, branch
`m3d-nano-target`, base `e31c1e8`. Only this report was written by reviewer.

Reviewed working blobs:

- `scripts/check.sh`: `33a967a236e6015c8efc05db23f300f5d62d1756`.
- `lakefile.toml`: `928f1c9d37e9ea115891a88f4f43135133f22356`.
- `test/nano-target/check.py`: `af6729e6622ad31e209f6923851234841c5f7c61`.
- `test/nano-target/fixture.py`: `def6483283b881495c131e0ae050111340812e4b`.
- `test/nano-target/test_contract.py`:
  `098d1755d1e6cd36e24241df01db4ac737eb6410`.

No gate-wiring findings. The sixteen new required paths cover both target
ports, test/executable roots, direct requests/observations, probe/replay
scripts, compressed packet fixture/checksum and fixture contracts.
Offline tests run unconditionally and propagate failure to the gate flag.
Both exact Lake executable targets have declared test roots and build with
`--wfail` in the existing Lean-present branch. The replay command runs only
after that build and propagates failure; it validates bounded compressed
fixture/checksum/provenance, atomically extracts ignored JSON, then executes
the direct and packet check binaries with explicit timeouts and checked
exit codes. Neither newly added ordinary-gate command fetches source data,
compiles OCaml, runs upstream or accesses the network. Existing explicit
missing-Lean/skip behavior is unchanged.

Independent pinned-shell commands and actual exits:

```sh
nix develop --command bash -n scripts/check.sh
nix develop --command python3 test/nano-target/test_contract.py
```

Both exit 0. After the final strict-JSON test adjustment, reviewer reread
that adjustment and the fixture's nonfinite-rejecting parser, reran the
suite (exit 0) and rechecked all five blob identities unchanged. The offline
suite currently contains ten tests, including the
added nonfinite-JSON sensitivity; it is not the earlier nine-test revision.
Current fixture, provenance/configuration, case identity/order, pinned source
digests, event fields/counter range, duplicate keys, checksum, compressed and
expanded size bounds all pass. Reviewer did not run full local gate, build
the new executables, rerun their semantic replay, commit, push or remote CI.
Those evidence claims remain with the author/root. Main reconciliation with
the subsequently merged corpus gate is a separate required publication step.
