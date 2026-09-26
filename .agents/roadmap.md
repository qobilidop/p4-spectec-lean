# Roadmap

Deferred work, not execution authorization. Updated 2026-09-26.
Broader M3 remains paused; choose a bounded scope with the user before starting.
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
The design owns acceptance criteria; these are implementation stages, not
new execution authorization. Both core semantics and target composition must
close. Broader full-P4 M3 remains paused.

1. Build the complete obligation inventory and investigate reverse-proof
   composition and the known Nano target representation/ABI boundaries.
2. Certify a meaningful execution path in both directions with its dependency
   closure, using reusable support; include an actual relation certificate.
3. Extend to every definition and source representation in the Nano export,
   discharging builtin contracts and actual initialization assumptions.
4. Integrate the Nano target, discharge extern and observation contracts, and
   connect loading and packet execution to the whole-program consumer proof.
5. Close the completion checker, full-corpus replay, boundary mutations and
   review evidence required by the design.

Investigate the target blockers early even if target integration lands later;
do not postpone a feasibility question behind helper-proof counts.

## Candidate next work

The [certification discussion](notes/compiler-certification.md) preserves
advisory priorities. Machine-readable entry-point certificate coverage is
complete; [Status](status.md) owns the current documentation checkpoint.
Deferred priorities include broader representation adequacy, discriminating generator mutations,
consumer-guided wrappers, and measured maintenance across upstream changes.
These other priorities are not newly authorized implementation.

Further correspondence needs operation-specific builtin contracts, ordered
iteration, casts/subtype checks, indexing/slicing/membership, type parameters
and extern contracts. Select a useful entry point and account for its dependency
closure rather than count disconnected helper proofs. The first certified
relation should exercise its actual relation form.

Known runtime boundaries before broadening claims:
`Match.sub_`, `Match.check'` and `Subst.subst_typ_inner` retain legacy
fuel-zero fallback behavior outside the certified fragment; a nested source
tuple needs a representation distinguishing it from flattened products.
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
