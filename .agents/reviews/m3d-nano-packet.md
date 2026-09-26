# Independent bounded Nano packet replay review

Root read-only implementation review, 2026-09-25. Reviewed the packet probe,
runner, fixture contract, offline driver, Lean replay and mutation checks,
alongside the corrected dynamic target. No remaining findings within this
bounded checkpoint. This review is not a whole-target completion claim.

The probe wraps the actual pinned `Spec.Rel.nanoswitch_drive`, preserving
its call, exception and driver behavior. It records both typed inputs,
outputs in relation order, and exact before/after builtin counters. The
Lean replay uses those captured inputs rather than claiming Lean boot or
STF execution. Its callback interpreter preserves StateEval and uses explicit
fuel/nesting limits; exhaustion fails comparison. It compares all semantic
outputs using Runtime.Value.eq and the exact final counter. Public upstream
runtime failures collapse error kinds; the harness reports the actual Lean
tag without claiming internal-tag equality.

The guarded observation and direct-handler checks are important: these
unguarded programs discard the malformed receiver, so their final outputs
alone cannot detect an invented PACKET repair. The mutation test rejects
that repair on the guarded event. Separate mutations alter an expected
output, counter, source header bit, and the LOCAL constructor shape.

Earlier review findings are resolved: packet fixture source digests are now
checked against an independently derived exact-pin Git-object catalog, not
merely accepted as well-formed strings; compressed input is bounded before
reading it into memory. Duplicate keys and nonfinite JSON are rejected.
The source fixture remains lossless except recognized region-path
normalization. Its checksum and provenance are reproducibility checks, not
an independent mathematical oracle-correctness proof.

Independent commands in the pinned shells, all actual exit 0:

- `python3 test/nano-target/test_contract.py`: ten offline tests.
- `python3 test/nano-target/check.py`: 24 direct observations, six successful
  relation calls, one guarded runtime failure (Lean err), five rejected
  mutations.
- `python3 test/nano-target/run.py --upstream
  /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec --check`:
  24 exact-pin observations.
- `python3 test/nano-target/packet-run.py --upstream
  /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec --spec
  /Users/qobilidop/my/work/p4-spectec-lean/upstream/nano-p4-spec --check`:
  four exact-pin sessions. Both upstream commands' combined actual exit is
  recorded in ignored `.artifacts/root-oracle-final.exit`.
- Independently hashed all six program/STF Git objects at the full pinned
  revision and asserted equality with the fixture catalog.

Full gate, reconciliation with the corpus checkpoint and final-head remote
CI are separate obligations. Boot, driver/STF, transmission, typed Nano
Externs, v1model/eBPF and general packet coverage remain unimplemented.
