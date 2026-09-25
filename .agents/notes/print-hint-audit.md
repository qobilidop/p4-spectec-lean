# Print hint provenance audit

2026-09-25, pinned upstream `8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3`.
Independent read-only inspection and measurements, before the printer port.

## Observations

- All 190 full-P4 print hints are variant-case hints. Their expression
  forms are HoleE, FuseE, AtomE, TextE, SeqE and BrackE; there is no OtherH
  requirement in this pin and no definition-level print hint.
- An independent JSON traversal, resolving aliases and retaining type
  arguments, finds 567 distinct subtype pairs. Every shared constructor
  has identical source/destination print policy after erasing regions.
  This includes the thirteen instantiated `continueResult` pairs.
- All 2,120 variant cases have an existing origin case with the same
  print policy. All 7,447 CaseE nodes have notes naming variants directly,
  never aliases. Identical mixops in unrelated type families can still
  have different policies: lookup must retain the type identifier.
- These are measurements of the pinned export, not proofs about arbitrary
  future specifications or arbitrary externally supplied value notes.

The measurements used Python JSON traversal inside `nix develop`, reading
`gzip.decompress(exports/p4.al.json.gz)`; extraction is not necessary.
For each UpCastE, DownCastE and SubE, the audit recursively collected its
resolved source/target applications through tuple and iterator types,
deduplicated complete applications, and compared matching case hints.
The origin audit compared each case against its declared origin's case
with the same mixop. Source regions were erased, placeholder indices and
all hint syntax retained. The implementation must turn these measured
invariants into checked generator conditions before relying on them.

## Upstream evidence

- `pass/elaborate/elab.ml:1243`: a CaseE is assigned its case's
  `typorigin`, then cast to the expected type. Inheritance preserves both
  origin and hints (`elab_typcase_plain`/`elab_typcase`).
- `interp/interp-al/interp.ml:648`: CaseE evaluation attaches its type
  note; concrete variant casts preserve values and notes (493–600).
- `interface/p4/unparse.ml:133`: lookup uses the note's type identifier
  and case mixop; type arguments are not part of the lookup key.
- `lang/hints/alter.ml:148`: numbered holes leave the sequential cursor
  unchanged, fusion threads it, and sequence/bracket handling preserves
  the distinction between absent and empty documents.
- `interface/interface.ml:118`: the print builtin calls the printer
  initialized from the full specification's hint environment.
- `interface/p4/parser.mly:1889`: the explicit parser retag is on the
  `p4program` list, whose note is not consulted by case printing.

## Consequences

Generated ToValue uses the containing static variant type, whereas
internally constructed upstream values retain the origin note. Their
printing agrees under the measured policy invariant. Switching ToValue
to typorigin is unnecessary for this pin and would not reconstruct
arbitrary decoded input provenance. Prefer a checked policy invariant
over changing the generated representation.

Refine.Rel erases notes, so it alone cannot imply hinted-print equality.
Future refinement coverage for printing needs an additional invariant
about print policies, and an explicit contract for the hint environment.

## Reproducible printer observations

`test/print/probe.ml` links the built upstream libraries directly and
calls `hints_of_spec_al` and `pp_value`; expected strings are observations,
not a second implementation of printing. The fixtures contain complete
AL definitions and values, plus the upstream commit.

After the normal upstream build, regenerate or check with:

```sh
nix develop .#upstream --command python3 test/print/run.py
nix develop .#upstream --command python3 test/print/run.py --check
```

The runner checks upstream HEAD against the indexed submodule pin,
compiles only under `.artifacts/print-oracle`, and changes no upstream
sources. The ordinary Lean gate reads `test/print/observed.json` on every
invocation; its check is not hidden behind a cached `#eval`.

The twelve observed cases include mixed sequential/numbered holes,
fusion, empty sequence pieces, bracketed empty text versus silent atoms,
type-specific lookup and default fallback, a constant hint with an unused
unprintable struct argument, a nested hinted value, Unicode text and
mixed ASCII/non-ASCII case conversion. Regeneration followed by
`--check` succeeded. The Unicode cases exposed existing printer gaps:
upstream renders `éΩ` as the literal ASCII escapes `\195\169\206\169`,
and lowercases `MIXÉΩ` to `mixÉΩ`, leaving non-ASCII characters unchanged.
