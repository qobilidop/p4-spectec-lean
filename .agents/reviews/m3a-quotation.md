# M3A quotation review

2026-09-25, independent read-only reviewer `review_quotes`.
Scope: the independent comparison and sensitivity tests, the namespace
fix in `Codegen/Emit.lean`, regenerated `id.al`, Lake and gate integration.

One medium finding: compiling the checker does not run it. Fixed by
building `check-quotes` with `--wfail` and executing it explicitly in
`scripts/check.sh`; the reviewer re-read the gate and confirmed both
failures propagate to its verdict. No remaining findings.

The reviewer confirmed that derived equality preserves AST fields while
the local instances erase only regions and hint lists; source `VarD`
omission agrees with `Ctx.load_def`. Separate type/callable lookup fixes
both quotation and source placement. The synthetic regression covers a
shared type/function/metavariable name across files.

Checks inside `nix develop`: `lake exe check-quotes`, exit 0, all 342
definitions match; `lake env lean P4SpecTecTest/QuoteChecks.lean`, exit 0.
Existing macOS linker target-version messages were replayed. The census
and full gate were outside this review's scope.
