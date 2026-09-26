# Independent dynamic Nano driver review

Root review, 2026-09-25. Compared drive_pipe and the partial Io aliases with
their pinned upstream sources, read the direct oracle and Lean replay,
the actual-driver observation wrapper, schema-2 contract and mutation tests.
No semantic findings within this bounded increment. Gate wiring is a
subsequent root-authored change and needs separate independent review.

The driver constructs raw PacketIn state and invokes exactly NanoSwitch_drive
with context and that state. It retains architecture, original input port
and original payload bytes; only the exact optional FORWARD mixop match
transmits. Noncase and singleton-sequence decisions drop, matching the
upstream optional getter rather than inventing an error. Hex parsing and
callback outcomes preserve the existing checked state boundary. The explicit
signed-63-bit input-port domain rejects unsupported mathematical integers
without wrapping; failure is before the callback. Empty/odd/lowercase hex,
signed extremes, wrong output arity and allocation before failure are covered.

Actual evidence wraps Original.drive_pipe, recording full input and output
contexts/architectures, received packet, transmissions and counters. Expected
transmissions are not synthesized from relation decisions. The Lean replay
uses the real AL relation callback with explicit fuel and compares all
semantic outputs, exact transmissions and fresh state. It still starts from
upstream-captured booted contexts; boot, STF parsing, transmission backend,
verify and typed Nano Externs remain outside this checkpoint.

The schema-2 snapshot retains both relation and driver evidence without
dropping semantic fields. Its 8,510,069 expanded bytes require an explicit
16 MiB bound; the compressed bound remains 1 MiB (305,049-byte fixture).
Strict parsing and checksum/source provenance checks remain enabled.

Independent pinned-shell commands, all actual exit 0:

- `python3 test/nano-target/test_contract.py`: eleven offline tests.
- `.lake/build/bin/check-nano-driver`: eleven direct observations.
- `python3 test/nano-target/check.py`: inherited 24 direct observations,
  six successful relation and driver calls plus the guarded failure, five
  inherited mutations and two additional driver mutations.
- Upstream shell: `python3 test/nano-target/run.py --driver --upstream
  /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec --check`:
  eleven original-driver observations.
- Upstream shell: `python3 test/nano-target/packet-run.py --upstream
  /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec --spec
  /Users/qobilidop/my/work/p4-spectec-lean/upstream/nano-p4-spec --check`:
  all four exact-pin sessions. Combined actual exit is recorded in ignored
  `.artifacts/root-driver-oracle.exit`.

No full gate, current-main reconciliation or remote CI is claimed here.
The comparison still uses Runtime.Value.eq for semantic values, not note or
value-cache identity equality; the direct stub checks selected type notes.
