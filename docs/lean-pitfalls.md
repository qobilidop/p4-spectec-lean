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
- Deriving `ToJson` for the IL mutual AST block fails on this toolchain: a recursive `subcheck` call targets the `typ'` helper. The independent quotation test uses derived `BEq` instead; nested-inductive opacity is harmless for an executable check.
- An object stored in an `initialize`d `IO.Ref` is marked thread-shared on `set`, and the runtime never treats a thread-shared object as exclusive (`lean_is_exclusive` is false for it): a `Std.HashMap` kept in such a cell copies its whole bucket array on every `insert`, quadratic in the entry count, however the cell is taken or modified. Keep a `Lean.PersistentHashMap` there instead (an insertion copies one path), and expect every object reachable from the cell to pay atomic reference counts afterwards.
- A call wrapped by a definition with `@[implemented_by]` inside a `partial_fixpoint` body (`memoRun name keys (f.run args)`) fails monotonicity ("Cannot eliminate recursive call ... enclosed in") even when the wrapper is the identity by `rfl`: the derivation matches registered lemmas, not definitional unfolding. Register one with `@[partial_fixpoint_monotone]` whose proof is the hypothesis itself. `unsafe` cannot appear in the type of an `initialize` declaration; keep the table type safe and the casts in the implementation.

## Writing tactics

From the rung 3 driver (`P4SpecTec/Tactic/Refine.lean`), 2026-09-25:

- A long list literal elaborates into nested `have` chunks, so a tactic walking `List.cons` in a definition's value sees `have`s; emit an explicit `a :: b :: []` chain (and raise `maxRecDepth`).
- `simp` with `decide := true` over big terms times out at `whnf`; rewriting under `decide` with a non-reducible definition leaves an ill-typed term. Mark smart constructors `@[reducible]` instead.
- Definitions matching on a projection (`match v.it with`) get conditional equation lemmas (`v.it = C … → f v = …`) that `simp` cannot use; unfold them by name.
- A named hole `?x` reused across two `cases` in one tactic run refers to the first goal of that name; use anonymous `?_`.
- `cases` on a fuel inside a match alternative or continuation copies the whole remaining proof into a zero branch that does not diverge; split fuel only at the head.
- Hypotheses left by `cases` are inaccessible, so `mkIdent userName` cannot reach them; build terms from `FVarId`s. Tactic error recovery can admit goals silently: wrap a custom tactic in `withoutRecover`.

From field-update certificate sensitivity tests (2026-09-26):

- `refine_al` infers the generated library from the theorem's declaration name, and uses it to find quoted definitions and generated value encoders. Replaying an emitted proof under an arbitrary scratch theorem namespace can fail even for an unchanged function. Give the replay theorem a fresh name under the original generated library, keep its original `HoldsSpec`, and change only the executable helper reference. Require the baseline proof and source-quotation equality to pass before interpreting a mutant's failure.

From compiled coverage checking (2026-09-26):

- A standalone executable's `importModules` environment did not expose all notation elaborators needed by `elabType`, even with `loadExts` and initializers enabled. The same checker passed under Lean's normal frontend. `check-coverage` therefore invokes the pinned sysroot's `lean --stdin`, imports its compiled test runner and checks fresh metadata in `run_cmd`. Keep the child exit status and escape interpolated arguments as Lean strings; do not bypass type checking or cache an earlier elaboration verdict.

From the N3 relation-premise certificates (2026-09-27):

- In `do` notation, `(← act)` is lifted out of the enclosing expression and runs before it, so `c && (← act)` does not short-circuit: `act` runs even when `c` is false (even `false && (← act)`). A side-effecting tactic step there silently runs at the wrong time. Write `← (if c then act else pure false)`.
- A tactic quotation `intro rf_ne` introduces a hygienic, inaccessible name; a later lookup of `` `rf_ne `` by user name finds nothing. Use `intro $(mkIdent `rf_ne):ident`.
- A goal-list snapshot taken *after* a `have … := … ?_` includes the new hole; restoring it on failure leaks the hole into later steps. Make each attempt atomic with a saved state instead.

From N3 iteration tooling (2026-09-27):

- A heartbeat or recursion limit is a *runtime* exception: `try … catch` in `TacticM` does not catch it (use `tryCatchRuntimeEx`), so a custom tactic's own error context is lost and Lean reports the timeout at the declaration. `refine_al.trace` now prints the goal whose normalization exhausted the limit.
- To iterate on a tactic, do not `lake build` a certificate: that rebuilds its whole dependency chain against the new tactics. `scripts/replay-cert.py` re-elaborates a scratch copy against the existing generated `.olean` files, so the cost is the proof itself (tens of seconds for most certificates; minutes for a heavy one at a large heartbeat budget). Use `--heartbeats` to fail fast and `--only` to keep selected theorems. It is faithful only for tactic-only changes; see its docstring.

From N3 core coverage (2026-09-28):

- `simp` rewrites inside binder types of the goal, so a relation stated as a `fun` in a pending `∀ a b, R a b → …` is normalized before the tactic introduces it. When later steps must read the relation's structure back (column encoders), state it through a named definition the simp set does not unfold (`ColumnRows`) and unfold it only where a value is proved.
- An unconditional equation `f (n + 1) … = match … with …` for a fuel-indexed interpreter function also fires under binders, on patterns bound inside a traversal of unknown values. Each available successor layer of the fuel unfolds again, so the goal grows exponentially without progress (the `maximum number of steps` failure). Guard such unfoldings with a simproc that fires only on concrete arguments (`assignExpConcrete`). Normalization merges successors, so a fuel appears as `n + k`, not only `n + 1`.
- A non-recursive encoder defined by pattern matching has no equation lemmas unless requested; `simp only [f]` then delta-unfolds it into a `match` on a still-unknown argument, copying every alternative into each fact that mentions it. Pass its constructor equations (`eqnsOf`) instead.
- Words that our own `elab` rules use as atoms (`columns`, `subtypes`, `iteration`) become tokens in importing modules and can no longer name a binder there; `instance` and `syntax` are keywords too.
- Case splits on a generated variable with many constructors multiply the whole refinement goal. When the generated code only tests the variable (`Eval.check (match x with …)`), prove the reference test equal to the generated test in a small side goal (the constructor split happens there) and split on the Boolean alone (`alignTest`).
- One checkout, one `lake build`: a second build (even `lake build P4SpecTec` for a quick check) rebuilds or deletes object files the first is using, and replays read them too. Use a separate worktree with its own `.lake` for concurrent replays, and do not `pkill` with a pattern that also matches replay copies under `.artifacts/replay/`.
- `simp`'s discrimination tree does not see through an instance projection: a lemma about `canon (ToValue.toValue (f x))` never fires on `canon (T.toValue (f x))`, the form an unfolded constructor encoder exposes. State such bridges also with the nominal encoder (the generated `canon_encoder` twins of `canon_toValue`).
- A decided fact whose left side is closed (`1 = xs.length`, from an interpreter check `1 = |xs|`) used as a `simp` rule rewrites that constant everywhere, including fuels (`n + 1` becomes `n + xs.length`), until the recursion limit. Use it reversed.
- Core `List.elem_cons` leaves `match a == b with | true => true | false => …`, which never meets the reference's `List.any_cons` disjunction; normalize with an `||` form (`elem_cons_or`).
- Functions defined by structural recursion through `flatMap f` (such as `Mixfix.args`) are well-founded, so evaluation (`decide`, `rfl`) gets stuck on them; write a structural twin by nil/cons and prove it equal. String comparisons over quoted specifications do reduce, but only the kernel sees through the transports in `String.decEq`: use `decide +kernel`, which adds no axiom.
- `induction h using T.rec (motive_1 := …)` with an explicit first motive fails ("expected resulting type of eliminator"); `revert` the extra premises so the goal is the first motive, and give only the nested motives. The nested motives' premises arrive as additional case arguments, so name them in the alternative (`| cons _ _ ih₁ ih₂ all c member => …`).

From proof-build performance (2026-09-28):

- Lean elaborates a module's theorem proofs in parallel, but anything that forces the kernel environment waits for every earlier proof still being checked, and silently serializes the module. Traps hit here: `Environment.constants` (use `getLocalConstantInfos` and the imported module data, `Tactic/Constants.lean`); `#audit_axioms` directly after its theorem (the generator places audits at the end of the scope); and elaborating a global name inside a namespace. Name resolution tests `Ns.X` and private candidates first, each missing candidate is checked against the reserved-name predicates, and for a name like `….match_rule.eq_1` the matcher predicate reads a synchronous environment extension. Build simp sets from constant names (`prepareSimpSet`), not identifier syntax. To find such a wait, check `real` against `user` time, then `sample` the process and look for `lean_task_get`.
- Carrying closed `simp` results across calls remains kernel-checked, but cache completeness depends on every selected rewrite fact and the discharger's context. Even an open selected fact (`n = 0`) can enable a conditional closed rewrite; reducible aliases evade the syntactic `Simp.isEqnThmHypothesis` test; local lets change definitional equality. Keys retain selected fact types, alias/unknown proposition hypotheses and local let identities/types/values. Only direct rigid Eq/HEq/And/Or/True/False heads may be omitted from discharge-only keys. Harvest only closed terms, normal forms and proofs whose constants are imported: backtracking can roll back newly realized constants. See `Tactic/Refine/Normalize.lean` and its regressions before changing these boundaries.
- Formatting a caught `simp made no progress` error with `MessageData.toString` cost about 1 ms per call, a quarter of a certificate's normalization time. Format only when tracing.

From polymorphic source-domain proofs (2026-09-29):

- Adding the recursive `repeat_` equation to `simp` unfolds calls on unknown predecessor counts without stopping at the induction hypothesis. Use `rw [repeat_] at run` once per induction case, then simplify only nonrecursive checks and numeric conversions before applying the hypothesis to the successful tail.

From the NanoSwitch target proofs (2026-09-29):

- `cases h : m.run` on `m : Eval α` does not rewrite a goal stated through `tryCatch` or bind on `m`: the goal mentions `ExceptT` operations, not `m.run`. First `change Option.bind m.run _ = _` (after unfolding `ExceptT.tryCatch`), then case on `m.run` (`Refine/Extern.lean`, `run_catchUnmatch`).
- The atom type's derived `BEq` has no `LawfulBEq` instance, so `simp` leaves `Keyword "PACKET" == Keyword "PACKET"` unsolved; use `simp +decide` for such closed comparisons.
- `Lean.Json.parse` does not reduce by `rfl` or `decide`. Keep proofs abstract over a decoding hypothesis and test concrete decoding with `#guard`.
- Do not predict `#print axioms` output: even an `rfl` proof about a structure literal can depend on `propext`, `Classical.choice` and `Quot.sound` through its definitions. Build first, then copy the message into `#guard_msgs`.

From the whole-program evaluator (`P4SpecTec/Tactic/LazyEval.lean`, 2026-09-30):

- `partial_fixpoint` definitions are irreducible and their value is `Lean.Order.fix`, which neither `decide`, `rfl` nor the kernel reduces; unfold them by their `eq_def` equation. `Lean.Json.parse` and `Lean.Json.compress` are `partial`: no proof computes them at all.
- `Lean.Meta.mkEqTrans` returns the other proof when one side is `Eq.refl`, so it cannot anchor a definitional gap between two steps; build `Eq.trans` directly.
- The kernel's lazy delta unfolds the side with the greater definitional height. Checking a gap between a low-height term (a bind, a recursor) and a well-founded fixpoint application unfolds the fixpoint through `WellFounded.fix` and its accessibility proofs, exponentially in the recursion depth: a 64-element `Array.mapM` timed out. Abstract the fixpoint constants shared by both sides of the gap into variables.
- Meta folds natural-number arithmetic only on terms without free variables. With a free `x`, `decide ((#[x, false].size : Int) < 2 ^ 62)` recursed in unary until `maxRecDepth`, although the size is 2. Replace free variables by temporary axioms (inside `withoutModifyingEnv`): Meta treats constants as ground, and the kernel never unfolds an axiom.
- `setReducibilityStatus` is global: marking `Nat.instMod` irreducible stalled every later `UInt8.ofNat`. Keep the kernel's native `Nat` operations reducible on literals. `withCanUnfoldPred` works per call but disables the `whnf` cache, which made evaluation impractically slow.
- A tactic run inside `withoutModifyingEnv` (`omega`, `simp`) may add auxiliary lemmas that the restored environment discards; inline them into the proof first, reading them with `getConstInfo`, since `Environment.find?` may not see an asynchronously added lemma.
- Output of `IO.println`/`IO.eprintln` during command elaboration is captured as messages and only appears at the end; for live progress, append to a file handle. `Expr.sizeWithoutSharing` is exponential on a shared proof DAG.

From recursive state run-soundness (`P4SpecTec/Tactic/StateGroupSound.lean`, 2026-10-05):

- Lean cannot derive `partial_correctness` for every `partial_fixpoint` definition: with eight parameters the derivation fails ("please report this issue") because instance resolution does not find `CCPO` of the long function type. `Lean.Order.monotone`, `admissible_apply` and the like fail the same way when their instances are left to resolution. The definition's value still is `Lean.Order.fix F hmono` with the instance as an argument, nested `instCCPOPi` and `instCCPOPProd`: read instances off it and apply `fix_induct` directly.
- The order of a mutual `partial_fixpoint` group's tuple is Lean's, not the source's. A member's position is the projections in its own value.
- `simp_all` uses every hypothesis as a rewrite rule. An induction hypothesis `∀ args, run = some _ → R args` rewrites each fact `R args` obtained from it to `True` and drops it, and facts of the selected path rewrite inside a retained failure. Keep such hypotheses behind a structure (`Refine.Kept`) and large retained terms behind a local definition, which `simp_all` does not enter and definitional comparison sees through.
- `simp only` with a rule for `<|>` also rewrites inside both alternatives (it inlines `have`), so a rejected alternative no longer is syntactically the definition's term. Apply the rule as a term, `(rule _ _ _).mp h`, when a subterm must survive verbatim.
- Comparing two different definitions applied to arguments unfolds both before failing. `assumption` on `f args = some _` took a minute against another function's run equation; filter hypotheses by head symbol first. Unifying a large term with a definition applied to metavariables is as bad (one case took two minutes): apply the definition to known arguments and compare closed terms.
- Elaborating a term whose type is as large as a group of definitions (`refine ⟨lemma h, ?_⟩` against a goal containing the unfolded functional) took minutes in unification. Build such terms with `mkAppOptM` and assign them; the kernel's check is fast.
- A nested action in a condition, `if a && (← act) then`, is hoisted before the whole `if`: `act` runs even when `a` is false. Bind it in the branch.
- `whnfR` unfolds `Unit` to `PUnit`; test for `PUnit`.
- A proof elaborated by `elabCommand` inside `run_cmd` may run in a task: its error is not in the command's own message log (it is reported for the file), and a later command in the same `run_cmd` sees the theorem as declared. A proof that failed to elaborate depends on `sorryAx`; one the kernel rejected is an axiom under its own name, which `#print axioms` of its users then lists. Set `Elab.async` to false in the scope for commands elaborated this way, and stop at the first logged error.
- `local`, `instance` and `structure` are keywords and cannot be variable names; a term after `exact` on the next line at a smaller column than `exact` is not parsed as its argument inside a nested `by`.
