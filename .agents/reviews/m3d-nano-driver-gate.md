# Independent Nano driver gate review

State_props review, 2026-09-25, limited to root-authored gate wiring.
The reviewer authored the driver implementation; this is an independent
review of the separate root-authored gate delta, not a self-review claim
for driver semantics. No implementation files were changed or staged.

Reviewed blobs:

- `scripts/check.sh`: `098dd3d1c12d5f20a81d99aec992c42912340148`.
- `test/nano-target/check.py`: `038a6629334600817b94c76acc4f17acc438b97b`.

No findings. The five required paths cover the new partial Io module,
Lean executable root, direct upstream probe, requests and durable observations.
The explicit `lake build --wfail` tools step builds `check-nano-driver` before
the Nano replay harness invokes its absolute binary path. The invocation has
the repository working directory, a 30-second timeout and `check=True`; a
missing executable, nonzero exit or timeout cannot silently pass. The existing
shell harness records replay failure in its final failure status. Existing
primitive and real packet replay calls remain intact. This introduces no
network or OCaml invocation into the offline gate.

Independent focused commands in the pinned nano-driver shell all exited 0:

- `bash -n scripts/check.sh`.
- `python3 test/nano-target/test_contract.py`: eleven tests.
- `python3 test/nano-target/check.py`: 24 inherited direct observations,
  eleven new driver observations, six successful relation/driver events and
  one guarded failure (Lean err), with the inherited and driver mutations.
- Scoped `git diff --check` for both gate files.
- An in-memory mock of the second subprocess separately raised
  `CalledProcessError` and `TimeoutExpired`; both propagated without invoking
  the later packet subprocess. The mock also checked the exact absolute
  executable, working directory, timeout and `check=True` arguments.

No full gate, current-main reconciliation, commit, push or remote CI was
performed by this review. The separate root semantic report
`m3d-nano-driver.md` records the implementation/oracle review and its limits.
