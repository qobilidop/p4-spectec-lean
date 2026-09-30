# Nano-P4 certification implementation plan

Active plan, compacted 2026-09-29 after N4 closed. N0–N4 are complete. The user authorized
N5 and N6 on 2026-09-30; N5 is implemented on `n5-consumer` ([consumer note](nano-consumer.md)).
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
  N2 remote gate once read an ignored raw export); profile proof costs before expanding
  expensive recursive groups.
- Extern-dependent claims assume the contract `NanoP4Target` discharges; print-dependent
  claims assume the pinned empty print hints. Target constraints are in
  [nano-target.md](nano-target.md).

Primary surfaces: `Codegen/`, `Refine/`, `Tactic/`, `BackendSim/`, `NanoP4Target/`,
`P4SpecTecTest/` and `scripts/nano-certification.py`.

## N5. Demonstrate a whole-program theorem

Use a small Nano parser/control filter whose packet-field test decides forward versus
drop, with actual extraction. The candidate is pinned `positive/src-addr-filter.p4`: the
parser extracts the Nanonet header, a source-address table allows addresses 1 and 2,
denies 3 and drops by default; its STF forwards `000100` unchanged and drops `000300`
and `000A00`, and the session replay covers it.

Prove the exact port/payload outcome for a stated family of valid packets and a drop
family, from the exported program and real initialization, including the composed
reference statement (`initializedSessionCorrespondence`), not only generated values.
Packets are unmodified upstream; state that rather than inventing rewriting. Keep
intermediate and sequential-call evidence so discarded receiver corruption cannot pass.

Exit: a checked consumer certificate with a walkthrough and distinguishing mutations of
source identity, packet branch, extern result and output/state, consuming library
contracts without duplicating semantics or assuming missing obligations.

Status 2026-09-30: implemented as `ExampleProofs/NanoP4SrcAddrFilter/` with `lazy_eval`; the
family is every three-byte packet (forward exactly for sources 1 and 2) and every shorter
packet, under the named `PacketStateText` premise. Payloads are outside the family. Review,
full gate and CI pending ([consumer note](nano-consumer.md)).
Main risk: symbolic header bits through generated parser and table code; `native_decide`
is not allowed, and deciding all 256 source values in the kernel may be too slow. Spike
one concrete drop case end to end first.

## N6. Close release evidence

Make strict combined completion (`--require-complete all`) a required part of the gate.
Audit the final manifest against source, signatures and design criteria; verify scope has
not narrowed. Keep partial-coverage diagnostics useful without weakening Nano's gate. Add
cross-layer mutations for alternative ordering, hard-error retry, omitted constructors,
wrong quotations, incompatible print provenance and corrupted target state, naming the
check that rejects each. Record generation, proof-checking and replay costs separately;
resolve unexplained regressions without weakening statements. Update the guide and README
only to delivered claims. Independent review, the full gate and exact-revision CI must
pass before declaring the milestone complete.

## Effort history

A 2026-09-27 forecast estimated N3 16–32 hours (revised 30–45), N4 12–24, N5 4–8 and N6
4–8, with moderate-to-low confidence. N4 took one working session: the feared mismatch
between stateful callbacks and a pure extern interface did not arise, because Nano has no
fresh state; the real blockers were a fixed-fuel trampoline and compressed-text payload
equality. Counts of definitions or obligations are not effort percentages.
