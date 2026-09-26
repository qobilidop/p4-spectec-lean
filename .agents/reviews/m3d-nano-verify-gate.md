# Shared verify gate-wiring review

Independent read-only review of root's narrow gate/Lake wiring, 2026-09-25.
Only this report was written during the review. This reviewer authored the
separately root-reviewed specification guard; this report does not claim
independent authorship review of that guard or a new semantic verify audit.

## Findings

No gate-wiring findings.

- Twelve new required source/probe/fixture/contract/guard paths fail loudly
  when absent, using the existing required-input gate mechanism.
- Both seven verify fixture contracts and six exact-spec guard contracts
  run unconditionally with the existing failure flag propagation.
- Lake registers `check-nano-verify` at the correct test-only module; the
  gate builds it with `--wfail` and executes it with failure propagation.
- The executable consumes committed observations and checks nineteen direct
  cases, five mutations and the recorded Nano AL incompatibility boundary.
  Ordinary CI does not invoke OCaml capture, `run.py`, the upstream shell,
  a spec checkout fetch or network operations.
- Existing driver, target, packet and general checks remain in place. No
  capture/fixture semantics, fuel bounds or failure comparisons are changed
  by this gate-only addition.

## Independent focused checks

Pinned `nix develop` shell in the isolated Nano-verify tree:

- `bash -n scripts/check.sh`: exit 0.
- `python3 test/nano-verify/test_contract.py`: seven tests, exit 0.
- `python3 test/nano-verify/test_spec_guard.py`: six tests, exit 0.
- `lake build --wfail check-nano-verify`: exit 0 (98 jobs).
- `lake exe check-nano-verify`: exit 0, nineteen direct observations match,
  five mutations rejected; Nano has no function relation and the full-P4
  getter gives `unmatch` as recorded.

The chained focused check process actually exited 0. Darwin linker target
version diagnostics were replayed by Lake; no Lean warning/error or test
failure changed the verdict. No full gate or remote CI is claimed here.
Root owns full validation and reconciliation with later published main.
