# Nano-P4 certification implementation plan

Durable, closed 2026-09-30: the Nano-P4 milestone is complete at `42ffad6`. Retained for the
closed-stage index and the constraints that bind later Nano work. N5 is recorded in the
[consumer note](nano-consumer.md) and N6 in the [release note](nano-release.md).
Full-P4 M3 stays paused.
[Design section 9](../../docs/design.md#9-nano-p4-scope-and-acceptance) owns scope,
[Certification](../../docs/certification.md) owns delivered guarantees, and
[status](../status.md) owns the next immediate action.

## Baseline

The pins cover 350 source declarations: 162 types, eight schematic variables, 76
functions, 77 relations, 26 builtins and one extern relation. The completion inventory
has 888 obligations; after N4 only the four release-stage ones (N5 consumer, N6
sensitivity, review, release) are open. The corpus is 78 typing programs and 39 STF
sessions (74 packets), all with upstream observations.

## Closed stages

Each is published on `main`; N1–N4 cite their passing exact-revision CI, while N0 was
closed within later checkpoints and has no run of its own. Historical Git paths are
recovery pointers for detailed records, not live links.

| Stage | Delivered | Closure evidence | Detailed record |
|---|---|---|---|
| N0 | Complete obligation inventory and pinned corpus accounting | inventory CLI in the gate | `d85e82c:.agents/notes/nano-certification.md` |
| N1 | Reverse execution, recursive relation feasibility, unhinted printing, raw-extern runtime representation | `56cf92c`, CI 36290916636 | same |
| N2 | 162 source codecs, 26 builtin contracts, bounded 30-definition closure with call admission | `d85e82c`, CI 36316496027 | `d85e82c:.agents/notes/nano-certification-review.json` |
| N3 | Forward and reverse theorems for all 153 bodied definitions, run-soundness for all 77 relations, final source domains | `67f67ae`/`6ca3a22`, CI 36539336394 | `6ca3a22:.agents/notes/n3-source-domains.md`, `bd7ed63:.agents/notes/nano-certification.md` |
| N4 | Extern discharge, two-way session composition, whole-corpus replay, completion binding | `4535868`, CI 36592809255 | [nano-target.md](nano-target.md) |
| N5 | `lazy_eval`, whole-program source-address filter certificate, `check-consumer` | `034a90b`, CI 36692276571 | [nano-consumer.md](nano-consumer.md) |
| N6 | Cross-layer mutations, combined completion in the gate, review/release record, costs | `42ffad6`, CI 36697907550 | [nano-release.md](nano-release.md) |

N4 exit evidence: `NanoP4Target.externsContractHolds` (every related input, global context
satisfying the specification and trampoline fuel); `NanoP4Target.sessionCorrespondence` and
its initialized-environment corollary; both typing legs and `check-nano-sessions` matching
every corpus case (the gate runs the Lean executable `check-nano-sessions` through
`P4SpecTecTest/Oracle/NanoSwitch/Sessions/check.py`); `--require-owned N4` and
`--require-complete target` with 0 unresolved.

## Constraints that still bind

- Source domains follow the pinned constructor grammar, not permissive runtime subtype
  membership: numeric casts change tags, optional iteration makes `OptV`, and cross-tag or
  bare optional membership remain counterexamples to identifying the two. Call and
  producer certificates establish composition; membership never supplies source validity.
- The evaluation domain is the runtime-inclusive profile wherever raw externs reach it
  (decisions, "Runtime-inclusive evaluation domain"); the raw carrier stays outside the
  source `value` grammar.
- Parameter codecs, dictionaries and independent admission predicates stay explicit;
  repetition proves successful-output preservation, not totality. Tuple results use exact
  dictionaries; closed right products that ambient encoding would flatten are rejected.
- Prove invariants at initialization and preserve them at every call; add no hypothesis an
  actual caller cannot establish. Extend both directions together; keep ordered attempts,
  negative premises and run-soundness; prove determinism only where needed.
- Reachable legacy matching/substitution fallbacks must be replaced or proved unreachable
  on admitted domains before certifying them.
- Reusable support stays out of `ExampleProofs`; generated files are never hand-edited;
  missing observations are never successful replay; nothing is skipped as unsupported.
- Use the existing generator, libraries and colocated tests; add no parallel semantics or
  name whitelist for proof selection (eligibility follows source structure); keep actual
  counterexamples and trustworthy failure classifications.
- Warm artifacts must never be the only evidence that a fixture's inputs are available (an
  N2 remote gate and the first N6 release CI read an ignored extracted export too early; the
  gate now removes the extracted exports at its start); profile proof costs before expanding
  expensive recursive groups.
- Extern-dependent claims assume the contract `NanoP4Target` discharges; print-dependent
  claims assume the pinned empty print hints. Target constraints are in
  [nano-target.md](nano-target.md).

Primary surfaces: `Codegen/`, `Refine/`, `Tactic/`, `BackendSim/`, `NanoP4Target/`,
`P4SpecTecTest/` and `scripts/nano-certification.py`.

## N5 and N6 (closed)

The plans are recoverable at `bd8be30` in this file; evidence lives in the
[consumer note](nano-consumer.md) and the [release note](nano-release.md). What still binds:

- The whole-program family is every three-byte packet (forwarded exactly for sources 1 and 2)
  and every shorter packet, under the named `PacketStateText` premise; payloads are outside it.
- The parser discards extract's receiver, so receiver correctness rests on
  `NanoP4Target.externsContractHolds` and the target oracle, not on whole-program traces.
- The planned "hard-error retry" mutation was replaced by `failureKind` (a retried mismatch made
  an error): no convenient generated definition reaches an error in an earlier alternative.
- `--require-complete all --allow-unpublished` is the gate; any change outside `.agents/` leaves
  review and release pending until a new release is recorded.

## Effort history

A 2026-09-27 forecast estimated N3 16–32 hours (revised 30–45), N4 12–24, N5 4–8 and N6
4–8, with moderate-to-low confidence. N4 took one working session: the feared mismatch
between stateful callbacks and a pure extern interface did not arise, because Nano has no
fresh state; the real blockers were a fixed-fuel trampoline and compressed-text payload
equality. N5 and N6 each took about one working session on 2026-09-30; N5's cost was
the kernel-checked evaluator (gap abstraction against well-founded unfolding), not the
program. Counts of definitions or obligations are not effort percentages.
