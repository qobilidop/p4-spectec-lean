# Nano whole-program consumer (N5)

Durable, closed 2026-09-30: retains the N5 whole-program certificate's evidence, constraints
that bind later consumers, and review record. The user-facing account is in
[Certification](../../docs/certification.md#a-whole-program-example); the rationale for the
evaluator and the packet-text premise is in [decisions](../decisions.md) ("Nano certificate
shape and evidence").

## What is established

- `P4SpecTec.Tactic.LazyEval` (`lazy_eval`, `lazy_eval%`) evaluates generated code with
  kernel-checked proofs; unit tests in `P4SpecTecTest/Tactic/LazyEval.lean`, including the
  64-element `Array.mapM` regression that times out in the kernel without gap abstraction.
- `NanoP4Target.Packet`: `hexText`, `string_to_bits_hexText`, `bits_to_int_unsigned_bytesBits`
  and the `PacketStateText` premise with its evaluation rule; `NanoP4Target.Session` adds
  `Transmits`, `ReferenceTransmits` and `referenceTransmits`.
- `ExampleProofs/NanoP4SrcAddrFilter/`: the generated quotation, evaluation theorems
  (`forwardOne`, `forwardTwo`, `denyThree`, `dropUnlisted`, three short-packet drops, the STF
  session with its trace pinned as `stfTrace`: the outcome after initialization and after each
  packet), the `Certificate` and `referenceFilter`.
- `check-consumer` (identity, upstream observation of the whole trace, literal values, 7 exact
  claims elaborated in the root namespace) binds `profile:consumer`. At N5 the gate required
  `--require-owned N5` and ran the mutation suite (baseline plus six rejections); since N6 the
  combined completion check covers the N5 obligations and runs the mutation suite.

## Constraints that bind later work

- The domain is every host-range port with every three-byte packet and every shorter packet.
  Payloads need rules for symbolic array sizes, `Array.extract` over an append, and the tree
  decoder over a symbolic bit array; `omega` facts can already discharge the size checks.
- `PacketStateText` covers only host-range packet states; a theorem must not assume a broader
  JSON round trip. Rules must be proved lemmas or this premise, never axioms.
- The oracle decides only tests whose symbolic atoms all occur in the supplied facts; stuck
  bits of unconstrained header fields are left symbolic by design.
- `lazy_eval` counts its work against `maxHeartbeats`; the four-prefix STF trace needs an 8M
  budget. The budget is a resource limit, not a weakened statement.
- A mutation of the target is exercised on a copy in the probe namespace; the library
  instance is never edited by the runner.
- Extract's returned receiver is discarded when the parser returns (`packet_in` is only copied
  in), and every corpus program extracts once; no whole-program output or state observes it.
  Receiver evidence is the extern contract (every call) and the target oracle's direct extract
  observations; the `receiver` mutation shows the contract rejecting a corruption that every
  claim of the certificate, including its trace, accepts. Do not claim contexts hold receivers.

## Costs (2026-09-30, local)

At `0b10557` (with the four-prefix trace): rebuilding `ExampleProofs` with the tools took 69 s
wall (174 s CPU); the mutation suite took 22–43 s with warm builds; `--require-owned N5`
completion took 66 s in the gate; the full gate took 207.56 s.

## Review record

- `24d36aa`..`d7fac98`: independent read-only review (Claude Opus 5.5 subagent, no builds), no
  blockers. Findings and resolutions:
  - Receiver corruption untested and only the final STF context compared: the whole trace is now
    pinned and compared, and a receiver mutation added. It showed the documentation's claim that
    contexts hold extract's receiver was false (the parser discards it); the docs now say so and
    the mutation is rejected by the extern contract instead.
  - Claim names capturable in the example namespace: claims are elaborated in the root namespace
    without opens.
  - Compared values could be recomputations: `check-consumer` requires them to be literals.
  - Walkthrough command lacked its argument; status stale; uppercase hexadecimal unstated;
    library theorems lacked axiom audits; the completion checker always built the example;
    aux-lemma inlining compared with the wrong environment; runner used `lake exe` in parallel
    and a non-atomic write: all fixed.
  - Identity mutation runs a copy of the identity comparison (plus the real freshness check):
    documented. Generated `Program.lean` inside the example: recorded as an exception in
    decisions.
- `0b10557`: the same reviewer confirmed all twelve findings resolved and the receiver
  correction against the generated semantics (`NanoSwitch_setup`, `Copy_out_arg`). It asked for
  the plan's receiver criterion to be restated (done) and fresh timings (done).
