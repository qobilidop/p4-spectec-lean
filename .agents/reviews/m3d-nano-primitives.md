# Packet data and dynamic extract review

Independent root review, 2026-09-25. Scoped to Core.Object, NanoSwitch.Pipe,
NanoTarget tests and the 24-case primitive/direct-handler oracle. Actual
program packet replay, callback configuration and driver work are separate.
The initial direct observations passed, but subsequent real packet replay
exposed a shape bug missed by these mocks; see the follow-up below.

Root compared the new port against the pinned core/object.ml,
nano_switch/pipe.ml and extern.ml. Bit ordering, signed low-bit operations,
short nibble padding, payload byte truncation, record fields, callback
order and the raw ExternV output were compared with the implementation being ported.
The port preserves signed and inconsistent decoded packet records; it does
not silently normalize them. Array checks are operation-specific. Signed
63-bit addition occurs before the short-packet branch, including the
max-int overflow case. Out-of-host-domain values remain separately labelled
in the primitive API; errors never become successful empty payloads.

The handler uses one explicit StateEval callback sequence. Callback state
and mismatch/divergence propagate without resetting or repeating effects.
Its partial-module headers explicitly exclude verify, driver/STF execution
and a typed generated Externs adapter. The existing upstream result-type
boundary is retained, not silently repaired with PACKET.

Review requested checks of update_var_e's scope and header-name arguments;
the author added them to both oracle callbacks and the unit test. These
assertions check selected semantic arguments, not arbitrary note equality.
The direct-handler oracle intentionally collapses an OCaml array exception
only to Lean hard error, never mismatch. The primitive error categories
remain distinct. Provenance checking uses the existing exact revision and
four-file patch guard; it is not a cryptographic oracle attestation.

Independent commands, with this worktree as working directory:

- Default pinned shell: `lake exe check-nano-target`, exit 0, 24 Lean
  observations matched. Lake replayed native linker deployment-target
  warnings from the pinned toolchain; these were not Lean proof warnings.
- Upstream pinned shell: `python3 test/nano-target/run.py --upstream
  /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec --check`,
  exit 0, 24 exact-pin observations matched.

These independent commands preceded the additional callback assertions,
whose frozen rerun remains required. No full gate, CI, whole packet support,
typed-adapter fidelity or milestone completion is claimed by this review.

## Real-replay follow-up

The author's actual packet replay later found that LOCAL must be
`CaseV (Atom LOCAL)`, not `CaseV (Seq [Atom LOCAL])`. The upstream DSL's
constructor and generated scope encoder use the former. The permissive
mock extractor accepted both, while the initial Lean mock asserted the
incorrect shape. Thus the initial direct comparison was too weak at this
boundary. The corrected port and both callback oracles now require the exact
Atom shape. Root independently inspected that revision and reran both the
24-case Lean comparison and exact-pin OCaml observation check (exit 0 each).
The initial mock success remains insufficient evidence of packet agreement;
the separate real-replay review is `m3d-nano-packet.md`.
