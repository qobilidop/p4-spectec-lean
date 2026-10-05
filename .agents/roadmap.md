# Roadmap

Updated 2026-10-04. The Nano-P4 completion milestone closed on 2026-09-30 at `42ffad6`.
Full-P4 M3 is the active milestone, resumed on 2026-10-04; other backlog remains deferred.
[Status](status.md) owns immediate obligations, not this backlog.

## Milestones and entry points

- M1: Nano generation, kernel checking, export and differential replay closed.
- M2: logical relations, forward AL certificates and reusable support closed
  as a bounded fragment, not complete Nano certification.
- M3 (active): full-P4 export/census closed; the library generates and builds with
  executable definitions (2026-10-04), logical relations and an audited run-soundness
  theorem for each of the 256 relations (2026-10-05), which closes M3B, and a both-leg
  corpus sweep agrees with upstream. The durable corpus campaign, correspondence
  certificates and targets remain incomplete.
  [Full-P4 overview](notes/full-p4/overview.md) owns remaining phases,
  [corpus](notes/full-p4/corpus.md) the bounded replay/resume constraints,
  [state integration](notes/state-integration/overview.md) the retained versus
  archived implementation boundary, and [Nano target](notes/nano-target.md)
  the dynamic/typed target exclusions.
- M4: the first consumer proof was brought forward and completed
  ([evidence](notes/field-update.md)). Broader client libraries and interfaces
  remain open. The example/library separation is complete, not a new milestone.

## Nano-P4 completion milestone (closed)

[Complete Nano-P4 support and certification](../docs/design.md#9-nano-p4-scope-and-acceptance)
closed on 2026-09-30 at `42ffad6`. The design owns the acceptance criteria; the
[closed plan](notes/nano-certification.md) indexes each stage's evidence and the constraints
that still bind; decisions ("Scope and product") record the authorizations.

Its stages were the obligation inventory (N0), feasibility probes (N1), reusable contracts
(N2), full core coverage (N3), target composition (N4), the whole-program proof (N5) and
release evidence (N6). N1–N6 each closed with independent review and exact-revision CI, N0
within later checkpoints; the
[plan's index](notes/nano-certification.md#closed-stages) lists the commits and runs.

## Candidate next work

The [certification discussion](notes/compiler-certification.md) preserves
advisory priorities. Machine-readable entry-point certificate coverage is
complete; [Status](status.md) owns the current documentation checkpoint.
Deferred priorities include broader representation adequacy, generator mutation campaigns
beyond the selected N6 boundaries, consumer-guided wrappers, and measured maintenance across
upstream changes. Nano follow-ups: whole-program packets with payloads (evaluator rules for
symbolic array sizes, see [consumer note](notes/nano-consumer.md)) and proving the
`PacketStateText` premise by adopting total JSON printing and parsing in the target port.
None of these is authorized implementation.

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
