# Field-update timeout review

Independent read-only implementation review, 2026-09-26.

## Scope and verdict

Reviewed the working-tree diff from `a249f2c` for
`NanoP4Proofs/FieldUpdate/test/run.py` and `test_runner.py`.
No findings remain. The separate example-library rename is not part of
this review.

The fix retains a 60-second runtime-probe deadline and gives proof replay
a separate 300-second deadline. These are bounded process wall-clock
limits, not changes to Lean's unchanged 4M-heartbeat proof budget.
The generated scratch definitions, replayed theorem bodies, source-identity
check, intended diagnostic boundaries and JSON schema are unchanged.

Both timeout paths still raise `HarnessError` before a case can return an
accepted or rejected result. `main` fails the suite rather than counting a
timeout as evidence against a mutant. New tests cover both phases for all
four cases, exact default timeout routing, and explicit budget injection.
Existing stale-result, unrelated-error and missing-mutation checks remain.

## Independent validation

Commands ran from `/Users/qobilidop/my/work/p4-spectec-lean`, each under
`nix develop /Users/qobilidop/my/work/p4-spectec-lean --command`:

- `python3 NanoP4Proofs/FieldUpdate/test/test_runner.py`: exit 0,
  nine tests passed. The printed `baseline failed` is the intentional
  fail-closed unit case, not a validation failure.
- `python3 NanoP4Proofs/FieldUpdate/test/run.py`: actual exit 0,
  session 20332. Baseline proofs checked; behavior was rejected by
  `update_fieldValue.refines_group`, quotation by `compareSpecs`, and
  representation by `Scalar.sourceRel`. All four schema-1 results matched
  their expected boundaries.
- `git diff --check -- NanoP4Proofs/FieldUpdate/test/run.py
  NanoP4Proofs/FieldUpdate/test/test_runner.py`: exit 0.

The independent real suite ran under shared local load. Per-phase timings
were not measured by this reviewer. The author's overlapping timed run
reported a transient missing build artifact during its last case; that
infrastructure failure was rejected, not accepted as a mutation result.
The independent run above completed every case successfully.

## Limits and remaining obligations

This review does not establish CI performance from local timing or
re-review the underlying semantic proofs. The parent owns the full local
gate and remote CI validation. Both remain required before the milestone
can be declared complete; the increased bounded deadline still needs
confirmation on the remote runner that exceeded the original deadline.
