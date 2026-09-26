# Independent scalar representation review

Reviewed 2026-09-25 by the state-codegen agent, independently of the
Domain/Representation author. Scope: source-domain selection, representation
adequacy, decoder bounds, and observational injectivity. No source edits.

Reviewed file blobs:

- `NanoP4Proofs/FieldUpdate/Domain.lean`:
  `60e8d4d9c95f5721cdabd2eb28ba62e0b77c4bad`.
- `NanoP4Proofs/FieldUpdate/Representation.lean`:
  `c7ed4a5fd95b9c9e435dc365fd11c17f40dad77f`.

## Result

No findings in this bounded representation layer.

The independent source profile matches the clean pinned Nano source checkout
`60dfd9912011bd5b1746ac88b26b58f7b3981991`, also the worktree's gitlink:
`1-syntax.watsup` declares `nat W int` and `nat S int`;
`3.0-value.watsup` declares `_B bool`, `MATCH_KIND '.' nameIR`, and
`value nameIR ';'`; `2.0-domain.watsup` makes `nameIR` text. The independent
AL encodings preserve these argument positions and atom categories, including
the Boolean tag rather than a keyword. Their generated embeddings select the
corresponding actual constructors and encoder clauses.

The domain intentionally selects AL `Num.Int` payload representation, natural
widths and arbitrary byte names. It does not claim all AL numeric encodings,
range-valid P4 integers, parser validity or program typing. `SourceScalar` and
`SourceFields` are defined through independent encodings modulo `canon`, not
as generated encoder images. Canonicalization erases value notes and source
regions recursively while retaining the selected tags, payloads, names and
list order. Its coarser treatment of functions/extern JSON cannot conflate
members of this scalar profile, which contains neither constructor.

Coverage proves existence of the corresponding generated representation for
every member of the declared source predicates. The converse encoding-validity
theorems prevent a one-direction-only adequacy claim. Injectivity establishes
that different profile scalars/fields/ordered lists are not identified by
observations; duplicates remain allowed rather than collapsed. Decoder results
are stated for the explicit independent or generated encodings, not silently
for every representative modulo annotations. The `fuel + 5` scalar and
`fuel + 6` field bounds account for the generated text-alias chain; list
decoding maps with unchanged fuel, so there is no list-length restriction.

Every advertised theorem has an exact axiom guard. The case-specific unused
simp-argument linter suppression does not alter proof checking or axiom audits.
The observed axiom sets are exactly `propext`, `Classical.choice`, `Quot.sound`.

## Independent checks

Commands used workdir
`/Users/qobilidop/my/work/p4-spectec-lean-field-update` and the pinned shell
`nix develop /Users/qobilidop/my/work/p4-spectec-lean --command`:

- `lake build --wfail NanoP4Proofs.FieldUpdate.Semantics
  NanoP4Proofs.FieldUpdate.Laws`: exit 0, 76 jobs; rebuilt the frozen
  Representation dependency and checked its exact audits.
- `lake env lean NanoP4Proofs/FieldUpdate/Representation.lean`: exit 0,
  an independent direct re-elaboration of all representation proofs/audits.
- `git diff --check`: exit 0.
- Read the pinned source syntax, generated `3.0-value.lean` encoder/decoder,
  `Prelude.Value` list decoder and `Refine.Value` canonicalization directly.

This review does not establish reference execution termination, the assembled
consumer correspondence theorem, whole-program semantics or a full gate.
Those remain separate integration obligations.
