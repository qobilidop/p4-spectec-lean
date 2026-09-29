# Roadmap

Updated 2026-09-29. Nano work through N4 is authorized and N4 is implemented; other
backlog remains deferred.
Broader full-P4 M3 remains paused.
[Status](status.md) owns immediate obligations, not this backlog.

## Milestones and entry points

- M1: Nano generation, kernel checking, export and differential replay closed.
- M2: logical relations, forward AL certificates and reusable support closed
  as a bounded fragment, not complete Nano certification.
- M3: full-P4 export/census closed; production generation, effect integration,
  broader correspondence and targets remain incomplete.
  [Full-P4 overview](notes/full-p4/overview.md) owns remaining phases,
  [corpus](notes/full-p4/corpus.md) the bounded replay/resume constraints,
  [state integration](notes/state-integration/overview.md) the retained versus
  archived implementation boundary, and [Nano target](notes/nano-target.md)
  the dynamic/typed target exclusions.
- M4: the first consumer proof was brought forward and completed
  ([evidence](notes/field-update.md)). Broader client libraries and interfaces
  remain open. The example/library separation is complete, not a new milestone.

## Nano-P4 completion milestone

The next major milestone is
[complete Nano-P4 support and certification](../docs/design.md#9-nano-p4-scope-and-acceptance).
The design owns acceptance criteria; the
[implementation plan](notes/nano-certification.md) owns concrete deliverables,
dependencies and exit checks. The user approved autonomous implementation,
starting with N0/N1, then requested completion through N2. Both core semantics and target composition must close.
Broader full-P4 M3 remains paused.

The plan proceeds from the complete obligation inventory (N0), through early
reverse-proof/target/printing feasibility probes (N1), reusable contracts (N2),
full core coverage (N3), target composition (N4), the whole-program proof (N5),
and release evidence (N6). Target and consumer work begin alongside core work;
their integration exits depend on checked core contracts. N0 is implemented
and reviewed. N1 is closed in `ccb8859`, with independent review and successful
full local/remote gates: recursive reverse execution, actual relation probes,
printing dispatch and faithful runtime representation with contextual failure
checks. N2 implementation is validated at `76bed84`; closure is recorded at
`d85e82c`, with independent review, all 44 local gate stages and successful
[final CI 36316496027](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36316496027).
The user authorized N3 on 2026-09-27, starting from the Program_load/Expr_eval
checkpoint. N3-owned proof closure is complete at `67f67ae`, with passing strict
N3 checks, full local/main CI and independent review. [Status](status.md) records
the exact evidence and remaining full-stage obligations. The user authorized N4 on
2026-09-29; it is implemented on `n4-target` with every core and target obligation verified.
N5 and N6 remain planned.
The plan owns the [historical effort estimate](notes/nano-certification.md#historical-effort-estimate);
status owns the next concrete step.

## Candidate next work

The [certification discussion](notes/compiler-certification.md) preserves
advisory priorities. Machine-readable entry-point certificate coverage is
complete; [Status](status.md) owns the current documentation checkpoint.
Deferred priorities include broader representation adequacy, discriminating generator mutations,
consumer-guided wrappers, and measured maintenance across upstream changes.
These other priorities are not newly authorized implementation.

N3 now has both correspondence directions for all 153 bodied definitions and
source-domain proofs for the four final polymorphic shapes. N4 discharges the extern
contract, composes sessions and replays the whole corpus; the normal gate requires every
core and target obligation owned through N4. The whole-program theorem (N5) and release
evidence (N6) remain.

Known runtime boundaries before broadening claims:
`Match.sub_` and `Match.check'` retain legacy fallback behavior outside the
certified fragment; selected N2 paths avoid these fallbacks. Substitution now
uses a syntax-derived bound. Exact empty/two-field tuple dictionaries are
supported; closed right products that ambient encoding would flatten remain
rejected, alongside unsupported arities.
Type-fresh, printer and state constraints remain in their topic notes.

## Longer-term backlog

- Well-typed random P4 programs via p4smith or derivation enumeration.
- Generated IL semantics if upstream's meta-circular spec matures; a shallow
  program model with a proved connection; or a verified Lean P4 parser.
  These are separate semantic boundaries, not scheduled replacements.
- Upstream the JSON export patch and return the P4-SpecTec pin to upstream
  main when Nano lands there. External coordination requires its own scope.
- Improve generated readability and stable client wrappers when actual proof
  use demonstrates the need, without losing source provenance.

## Documentation site, when justified

Use one GitHub Pages site in the pinned Nix shell. API reference was planned
after M1 and remains deferred: use doc-gen4 in a separate Lake package under
`docs/api/`, published at `api/`, outside ordinary builds. At M4, a separate
Verso website package can place checked
examples beside the API site. Pin doc-gen4/Verso to the Lean toolchain.
Markdown remains the maintained design/working format until that work is
scoped; no site build is authorized by this plan.
