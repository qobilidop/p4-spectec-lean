# Review of M1 (branch `m1-nano-p4`)

Independent read-only review by a separate agent, 2026-09-25, of the
branch at `fb0ebc2` (before the mirrored modules moved to their upstream
paths; `Prelude/Builtins/` is now `Interface/Builtin/`, `Prelude/Value.lean`'s
mirrored part is `Runtime/Value/Value.lean` and its printer
`Interface/P4/Unparse.lean`, `IL/`, `AL/`, `Xl/` are under `Lang/`). The
disposition of each finding is at the end.

## Summary (reviewer)

The deep embedding mirrors `il/ast.ml`, `al/ast.ml`, `domain/atom.ml`, `domain/mixfix.ml` and `xl/*.ml` constructor for constructor and in order; the codegen reproduces the AL interpreter's sequential mode (group order, path order, else last; clause order, else last), the pattern shapes of `assign_exp`, the bounds checks of `eval_idx_exp`/`eval_slice_exp`, and the joint-iteration semantics of `Ctx.sub_list`/`sub_opt` (the algo pass's `guard.ml` does insert length and optionality guards for iterated expressions as well as premises). The five spot-checked definitions render their watsup rules faithfully, in order, with the AL's inserted guards. The harness compares against a recorded upstream verdict, not the folder name, and cannot mask a decode failure.

Two claims were not supported by the evidence: (1) the trusted prelude's `bitstr_to_int'` was a wrong port (fuel-bounded normalisation that silently returns an un-normalised value for inputs beyond one period; Nano-P4 never feeds it such inputs, so 78/78 could not see it), with no builtin unit tests although design 5.2 promises them; (2) the oracle was upstream's SL interpreter, not the AL interpreter the port mirrors (`nano check` ignored its `il`/`sl` flag), the verdict was pass/fail only, and `fail` on both sides conflated unmatch, error, crash and fuel exhaustion.

## Findings (reviewer)

1. **High** — `Prelude/Builtins/Numerics.lean` (`bitstr_to_int'`): fuel bound `log2 |n| + 2` where the OCaml needs about `|n| / 2^w` steps; wrong result, no `none`. Fix: closed form `Int.emod (n + half) w' - half`, plus `#guard` tests for every builtin.
2. **High** — `scripts/export-program.sh` records `nano check`'s verdict, and `nano.ml` binds the `il`/`sl` flag to `_mode` and hard-codes `SL_mode`, so every verdict was the SL interpreter's while the docs present the comparison as against the AL interpreter. Fix: make `check` honour the mode in the patch, record both verdicts, say which is the oracle.
3. **Medium** — pass/fail only: the `typingContext` output of `Program_ok` is never compared; upstream `fail` covers `Err`, `Unmatch` and OCaml exceptions (hidden by `2>/dev/null`); Lean `fail` covers fuel exhaustion. Fix: print output values from `check`, compare them, report fuel exhaustion separately, keep upstream's diagnostic beside the verdict.
4. **Medium** — `Codegen/Exp.lean`: division and modulus by zero give 0 (Lean) where upstream raises; `PowOp` is emitted although `Num.bin` has no such case (upstream raises). Neither in design 5.3/5.4.
5. **Medium** — `IfNotHoldPr` tests `isNone`, so a callee `Err` becomes a successful negated premise; the only site where the Err→`none` collapse changes a result's direction. Document; M2's monad must keep `Err` distinct here.
6. **Medium** — `SubE`'s `subcheck` is discarded; `is_S` checks the top-level mixop only. Loud at M1 (a pair whose argument types differ fails to elaborate) but the spec's own statement of what to check is dropped.
7. **Medium** — stale statements: `nano-p4.il.json` in README/lakefile/`P4Spec.lean`; README's "IL semantics … tactic" (M2); `docs/` listed twice; timing table with pre-rename names; status "3.1 s" vs table 3.40; design 5.2 row promising builtin unit tests; 5.3 rows describing M2 artefacts without a marker; `IL/Ast.lean` header saying "three" deviations where the design lists four; `check-mirror.py` docstring vs. behaviour.
8. **Medium/Low** — `print` ignores `print` hints and `String.escaped`; agreement rests on Nano-P4 declaring no hint. Fix: fail on any `print` hint until supported; port `String.escaped`.
9. **Low** — `check-imports.sh` grep unanchored after the rename commit.
10. **Low** — `iterPrem` with `Opt` and no bound variables binds `none` without running the premise; upstream runs it once and binds `some`.

Also noted: `Value.compare` on `ExternV` orders by compressed JSON (key-sorted) where upstream is order-sensitive; `Xl/Num.lean` does not mirror `compare`/`eq`/`bin`/`cmp` (they live in the prelude under Lean names); text `LenE`/`IdxE` count characters, bytes upstream; `Texts.text_to_int` narrower than `Bigint.of_string`; `Names.ctorName` not strictly invertible; `$default` emits an identity `List.map (·)`.

## Checked and found consistent (reviewer)

Mirrors of `il/ast.ml`, `al/ast.ml`, `domain/atom.ml` (`compare` reproduces `Stdlib.compare`), `domain/mixfix.ml`, `xl/*`, `util/source.ml`; `Value.compare`/`eq`; every builtin file function by function except the finding above; codegen against `interp.ml` and `ctx.ml` (sequential mode, group and path order, `assign_exp` shapes, bounds, casts, patterns, membership and equality by value, `RulePr` split, dotted `UpdE`); `guard.ml` inserts the joint-iteration guards; the five spot checks; the harness reads recorded verdicts and cannot mask decode failures; the gate and CI run the same script in the same shell.

## Disposition (2026-09-25, on this branch)

1. **Fixed.** `bitstr_to_int'` is the closed form `Int.emod (n + half) w' - half`; `P4SpecTecTest/Builtins.lean` holds `#guard` tests for every port under `Interface/Builtin/`, including the reviewer's `bitstr_to_int' 4 65025 = 1`.
2. **Fixed.** The patch makes `nano check` honour its `il`/`sl` flag; `scripts/export-program.sh` records the AL interpreter's verdict as `<name>.verdict` and the SL interpreter's as `<name>.verdict.sl` (identical on all 78); docs say the AL is the oracle.
3. **Fixed.** `check -json` prints the output values; `<name>.outputs.json` is recorded for every passing program and `nano-p4-run` compares the output typing context by `Value.eq` (48 of 48 equal); fuel exhaustion is reported as `fuel` (a second run at twice the fuel); upstream's first diagnostic is recorded beside a failing verdict.
4. **Fixed.** Division and modulus are hoisted through `Num.natDiv?`, `intDiv?`, `natMod?`, `intMod?` (`none` on zero); `^` is `Num.pow?`, `none`, since `Num.bin` has no case; both in the design's 5.3 row.
5. **Documented** in the 5.3 row: an `Err` inside a `does not hold` premise counts as the premise holding; the M2 monad must keep `Err` distinct there.
6. **Partly fixed, documented.** Codegen now asserts that a case shared by a subtype pair has the same argument types on both sides and fails otherwise; the `subcheck` itself is still not consulted (5.4 says so).
7. **Fixed.** README, lakefile comments, `P4Spec.lean`, the timing table (regenerated), design 5.2 and 5.3 markers, the `Il/Ast.lean` header, the mirror-check docstring.
8. **Partly fixed.** `String.escaped` is ported (`P4.Unparse.escaped`); codegen rejects a spec with any `print` hint until hint-driven printing exists (5.4).
9. **Fixed.** The import check is anchored (`grep -x`).
10. **Fixed.** An `Opt` iterated premise with no bound variable runs the premise once and binds `some`, as `sub_opt ctx []` does.

Also noted items: the `List.map (·)` identity is gone (a single binding variable takes the list directly); the others (`ExternV` ordering, `Xl/Num.lean` not mirroring the operations, text length in characters, `text_to_int` narrower, `ctorName` invertibility wording) are recorded as open threads in `.agents/status.md`.
