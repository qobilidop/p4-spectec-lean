# Print policy provenance

Compacted 2026-09-26 from `print-hint-audit.md` and review
`m3b-print-hints.md`, recoverable at Git `968ad65`. Recorded evidence is from
2026-09-25 at upstream `8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3`;
Durable provenance constraints with paused refinement work, not a fresh review.

Keep generated values' containing static type notes and check policy
compatibility. Upstream constructed cases retain origin notes; switching
ToValue to origins would not recover arbitrary decoded provenance. Lookup
must use type family and mixop; unrelated families can share a mixop with
different policies. Upstream lookup ignores type arguments, but the
compatibility audit must retain them.

Independent JSON traversal found 190 variant-case hints (HoleE, FuseE,
AtomE, TextE, SeqE, BrackE), no OtherH or definition-level requirement;
567 subtype pairs with matching shared-case policies (including thirteen
`continueResult` specializations); 2,120 cases matching origin policies;
7,447 CaseE notes directly naming variants. It resolved aliases/full
applications recursively through tuples/iterators, erasing regions only.
These are pinned measurements, not a theorem for future exports/external notes.

Codegen checks supported forms, origin/bridge compatibility and actual
variant/case notes, emits literal closed policies and rejects unsupported
forms, bounds errors or changed policies. Interpreter hints come from the
source spec. Confidence high at this pin; revisit incompatible exports.
Related constraints: [generated encodings](generated-encodings.md).

Source anchors under pinned `p4spec/lib`: `pass/elaborate/elab.ml:1243`
assigns origin before casts; `interp/interp-al/interp.ml:493–600,648`
preserves notes; `interface/p4/unparse.ml:133` uses type/mixop;
`lang/hints/alter.ml:148` distinguishes numbered holes from sequential cursor
advance and absent from empty documents. The parser's p4program list retag
does not affect case printing.

`test/print/probe.ml` invokes actual `hints_of_spec_al`/`pp_value`. After
upstream build, regenerate/check `test/print/run.py` in the upstream Nix shell.
It verifies indexed pin/HEAD and only builds ignored artifacts; ordinary
Lean checks read the fixture at runtime, not cached `#eval`. Twelve cases
cover cursor/numbered holes, fusion, empty pieces/brackets, silent atoms,
family lookup/fallback, unused unprintable arguments, nested hints, Unicode
and case conversion. Upstream prints `éΩ` as literal ASCII escapes
`\195\169\206\169` and lowercases `MIXÉΩ` to `mixÉΩ`.

Two GPT-6 Astra agents cross-reviewed, each excluding authored files: oracle
author reviewed alternation/policy validation, policy author reviewed
printer/dispatch/oracle, both reviewed root integration. Sol authored
alternation. No unresolved blocking findings. Fixes made CI compare the
recorded revision to actual HEAD instead of accepting any 40-character string,
and added unprintable/error-kind cases at printer/builtin/interpreter levels.
Printer failures are hard errors; unused unprintable arguments need not be
evaluated. The old hint-free introduction was corrected.

Independent Alter, PrintPolicies/emitted-table, twelve-output and upstream
regeneration checks passed. The 190-entry full-P4 table elaborated and matched
decoded policies after region erasure. Parent separately recorded full gate
exit 0 with pin/error regressions. This is bounded historical evidence.

`Refine.Rel` erases notes, quotations erase hints, and `HoldsSpec` alone
supplies no printer-environment contract. None implies hinted-print
correspondence. Preserve an additional policy invariant and explicit hint
environment contract before widening refinement or decoded provenance claims.
