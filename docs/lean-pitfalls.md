# Lean pitfalls

Traps hit while writing this repository's Lean, each verified on the
toolchain `lean-toolchain` names. Read before extending the code
generator (`P4SpecTec/Codegen/`) or the proof tactics
(`P4SpecTec/Tactic/`); add an entry when a new one costs more than a few
minutes. The deviations these forced on the design are in
`docs/design.md` section 5.3.

## Elaboration and syntax

Verified on leanprover/lean4:v4.34.1 (2026-09-25) while building the code generator:

- `deriving BEq` on a nested inductive (constructor holding `List T`) compiles without axioms but is opaque: `decide`/`rfl` cannot unfold it. Generate structural equality yourself if proofs need it.
- The kernel's nested-inductive check does not unfold `abbrev`s in constructor arguments (`phrase T` fails; spell `info T Unit region`) and rejects a `Prod` whose component is `List T` for a `T` being declared (`Nat × List Var` fails; make it a named inductive).
- Structural recursion through `List.map f xs` fails; write a helper `f_list : List T → ...` by nil/cons in the same `mutual` block. Recursion on a structure wrapping the inductive must pattern-match (`⟨v, _, _⟩`), not project (`v.it`).
- In `do`, `let C a b := v` defines a local function `C`; write `let .C a b := v` (add `| none` only if refutable, else "redundant alternative"). `guard (match x with ...)` fails to find `Decidable`; use an `if`-based helper on `Bool`.
- Structure-instance fields on continuation lines must start at the same column as the first field, or parsing stops with "expected '}'".
- A module docstring `/-! -/` must come after the `import` lines. `Std.Format.text "\n"` is a hard newline honoured by `nest`; `Format.line` in a group may flatten to a space.
- `Lean.Parser.getTokenTable env |>.values` lists tokens; run the extraction from an `#eval` in a file that imports all of `Lean` (`importModules` in a `--run` main sees fewer).
- API drift: `String.drop`/`dropEnd` return `String.Slice`; `String.get`/`String.mk`/`List.asString` deprecated (use `String.ofList`); core `Int` has `Int.not` but no `land`/`lor`/`xor`; `Lean.Json.compress` needs `import Lean.Data.Json.Printer`; `Json.getObjVal?` replaces map lookups.
- A binder named `at` or a field named `at` needs `«at»`; a pattern variable named `id` is ambiguous when a namespace defines `id`.

## Writing tactics

From the rung 3 driver (`P4SpecTec/Tactic/Refine.lean`), 2026-09-25:

- A long list literal elaborates into nested `have` chunks, so a tactic walking `List.cons` in a definition's value sees `have`s; emit an explicit `a :: b :: []` chain (and raise `maxRecDepth`).
- `simp` with `decide := true` over big terms times out at `whnf`; rewriting under `decide` with a non-reducible definition leaves an ill-typed term. Mark smart constructors `@[reducible]` instead.
- Definitions matching on a projection (`match v.it with`) get conditional equation lemmas (`v.it = C … → f v = …`) that `simp` cannot use; unfold them by name.
- A named hole `?x` reused across two `cases` in one tactic run refers to the first goal of that name; use anonymous `?_`.
- `cases` on a fuel inside a match alternative or continuation copies the whole remaining proof into a zero branch that does not diverge; split fuel only at the head.
- Hypotheses left by `cases` are inaccessible, so `mkIdent userName` cannot reach them; build terms from `FVarId`s. Tactic error recovery can admit goals silently: wrap a custom tactic in `withoutRecover`.
