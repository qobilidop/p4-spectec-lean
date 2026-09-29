# NanoSwitch target

Durable, updated 2026-09-29: owns the constraints of the concrete NanoSwitch target that
closed N4, and the N4 review record. The user-facing account is in
[Certification](../../docs/certification.md); reproduction belongs to the
[session replay](../../P4SpecTecTest/Oracle/NanoSwitch/Sessions/README.md),
[NanoSwitch target](../../P4SpecTecTest/Oracle/NanoSwitch/Target/README.md) and
[NanoSwitch verify](../../P4SpecTecTest/Oracle/NanoSwitch/Verify/README.md) oracles.
Full-P4 integration remains paused.

## What is established

- `P4SpecTec.BackendSim` ports pipe.ml's extract, `init_pipe` and `drive_pipe`, core
  verify, and make.ml's `call_func` failure collapse, generic in the effect carrier. The
  interpreter passes its own function evaluator at the remaining fuel as the trampoline.
- `NanoP4Target.externs` is the typed extern instance over the generated model;
  `externsContractHolds` discharges `NanoP4Spec.externsContract` for every reference
  configuration registering the NanoSwitch externs with guards off.
- `NanoP4Target.sessionCorrespondence` composes `NanoSwitch_init` and packet driving in
  both directions; `initializedSessionCorrespondence` and `sessionObservations` instantiate
  the concrete initialized environment. `check-target` checks their exact types.
- Upstream observations cover all 39 STF sessions (74 packets); `check-nano-sessions`
  matches them on both Lean paths, and the completion CLI verifies all 117 replay cases.

## Boundaries that must survive future work

- Extract returns raw `ExternV objectState`, written into the receiver; generated code
  carries it in the runtime-only `value` alternative. Restoring PACKET would repair
  upstream semantics, not port it. A reused receiver mismatches in `Callee_eval`; the
  direct handler rejects it as a hard error.
- A failed trampoline callee of either kind is an extern mismatch (make.ml `call_func`
  with interp `eval_func`). Lean cannot separate a nested target abort from AL `Err`;
  no Nano callee reaches an extern. Direct handler tests keep the callee's own kind.
- Extern payloads are decoded from their compressed text, because runtime equality and
  `Rel` compare payloads that way (design section 5.3); upstream compares Yojson trees.
  Unit tests and replay, not a parser proof, show target-serialized payloads round-trip.
- Packet operations keep signed or inconsistent decoded records with operation-specific
  checks; signed-63-bit addition precedes the short-packet branch; out-of-host values are
  target errors, not empty packets. Ports outside that range reject before callbacks.
- The driver transmits only on the exact FORWARD mixop; other decisions drop.
- The extern contract assumes every defined function's type parameters fresh (`X`, `K`,
  `V`), as the trampoline may call any defined function; session theorems assume the
  pinned empty print hints, which `check-target` confirms for the export.
- Upstream reports session failures only as a class and no corpus session fails, so
  failure kinds are compared between the Lean paths only. Sessions use only `packet` and
  `expect` STF statements; expectation matching stays upstream.
- Shared verify keeps the full-P4 getter ABI; Nano has no `ExternFunctionCall_eval`, so
  direct helper success is not Nano source-program verify coverage.
- Capture guards require exact pins and clean inputs; session values store cache
  identities as 0, since comparison is canonical.
- v1model/eBPF externs return ctx/arch/callResult and need their own faithful ports.

## N4 review record

All reviews were independent read-only AI reviews (Claude Opus subagents) without builds.

- `0416632` (extern discharge): one blocker, two Lean lines over 100 columns, fixed in
  `e88e8a0`. Suggestions adopted: per-clause freshness in the generated contract instead
  of union indexing, axiom audits for every helper, AGENTS.md library references, a
  corrected test comment, explicit universe binder, and stating that the reference port
  also decodes reparsed text. Semantics were found faithful to upstream.
- `ad1c4ab` (session composition): no blockers. Medium findings, resolved in `09cb951`:
  the decision value was only checked for consistency with transmissions (now recomputed
  on both paths and compared), and STF packet coverage was not gated (now required).
  Also adopted: initialization failure-kind comparison, a failing packet ending its
  session, gated upstream `pass` results, message-specific and dropped-packet mutations,
  README notes on canonical comparison and non-packet STF commands.
- `09cb951`, `a0f7c79` (hardening, completion binding): see status for the verdict.

Earlier bounded-target reviews and fixtures (primitive, driver and verify observations,
the four-session packet fixture) remain in the gate; their records are recoverable at
`02adefa:.agents/notes/nano-target.md`.
