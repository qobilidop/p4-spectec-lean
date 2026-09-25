# M2 phase D: rung 3 as built

Working note, 2026-09-25. What the refinement theorems look like, how
the driver tactic proves them, and what is outside its fragment. The
decisions here are copied into `.agents/decisions.md` at the checkpoint
that lands them; the artifact description goes to `docs/design.md`.

## Statement

Per definition `X` (a relation, a function or a table) in the fragment,
in `NanoP4Spec/Refinement.lean` (one module after every spec file, since
the theorems need the whole quoted spec):

    theorem X.refines (fuel : Nat) (cfg : Config) (ctx : Ctx.t) (internal : Bool)
        (hguard : cfg.guard = false) (hspec : HoldsSpec NanoP4Spec.spec ctx.global)
        (v0 v1 : value) (p0 : T0) (p1 : T1) (h0 : Rel v0 p0) (h1 : Rel v1 p1) :
        Refines (fun vs (o : S) => Outs vs [toValue o])
          (invoke_rel fuel cfg internal ctx (Q.i "X") [v0, v1])
          (ExceptT.mk (NanoP4Spec.X.run p0 p1))

- `Refines P m n`: every defined result of the interpreter's `m` (a
  success or a failure, never divergence) is matched by a defined result
  of the generated `n`, the same failure kind or values related by `P`.
  Divergence of the interpreter (fuel exhaustion) refines anything, so
  the theorem is about all fuels and the corpus runs are instances.
- `Rel v x := canon v = canon (toValue x)`: the IL value is the image of
  the generated value up to notes and regions (`Refine/Value.lean`);
  `Value.eq` is exactly canonical equality (`eq_iff_canon`).
- `HoldsSpec spec g`: the global tables hold every quoted definition of
  the spec as `Ctx.load_def` would enter it; `NanoP4Spec.spec` is the
  list of every `d.al` (types, relations, functions, builtins, externs;
  not `VarD`), emitted as an explicit `::` chain because the list macro
  chunks a long literal into nested `have`s.
- The guard is off (`cfg.guard = false`): the interpreter's dynamic type
  checks are instrumentation, not meaning; `internal` is arbitrary.
- A recursion group gets `X.refines_group : ∀ fuel, stmt_X fuel ∧ ...`
  by `Nat.strongRecOn` on the fuel, and a corollary per member; the
  driver uses the induction hypothesis for calls inside the group
  (`omega` discharges `fuel' < fuel`) and the callee's theorem otherwise.

## The tactic `refine_al`

`Tactic/Refine.lean`. Lockstep symbolic execution:

- The interpreter side is computed by `simp only` with the interpreter's
  own equation lemmas (`getEqnsFor?` of every function of the recursive
  block, which fire only on a successor fuel; the invocations
  `invoke_rel`/`invoke_func` are unfolded once, for the definition under
  proof) on the concrete quoted syntax, the runtime's helpers, the `Q.*`
  accessors, monad laws, list lemmas and the literal-deciding simprocs;
  `cases` on the fuel variable at the head of the chain, one level at a
  time, closes the zero case by `refines_diverge`.
- The generated side is walked: `have` binds its variable
  (`refines_have`); a call `ExceptT.mk (Y.run ...)` at the head is paired
  with the interpreter's `invoke_*` at the head through `refines_bind`
  and `Y.refines` (the value goals `Rel v x` go to the value prover); a
  `match`/`if` on a variable is split by `cases` on that variable; a
  `pure` against a `pure` reduces to the value prover; a `throw` against
  a `throw` is `refines_throw`; sequential choice is `refines_orElse`.
- Facts are `canon v = canon (toValue x)` with `v` an interpreter value
  variable. When the interpreter inspects such a `v` (a stuck `match` on
  `v.it`), the driver splits the generated `x` by `cases`, which is the
  case analysis the generated code performs too; after that `toValue`
  computes to a literal and the exposure lemmas (`canon'_eq_case`,
  `canonMixfix_eq_seq`, `canons_eq_cons`, ...) expose the shape of `v`.
- Table entries are derived lazily from `hspec`: a lookup
  `g.rtbl.get? "Y"` in the goal yields `hspec Y.al (List.Mem proof)`,
  unfolded to the entry.
- Equality tests: the interpreter's `Value.eq a b` is rewritten to the
  generated `Value.eq (toValue x) (toValue y)` by `eq_of_canon` before
  the condition is split; `Value.eq` on literals of base types decides.
- The value prover: `simp only` with the `toValue` functions and
  instances of the library, the `canon` family, `Make.*` and the facts as
  rewrite rules, then `rfl`.

Everything the tactic cannot close fails the build; nothing is `sorry`ed.

## The fragment

Decided syntactically by `Codegen/Validate.unsupported`, closed under
callees (a definition whose callee has no theorem has none), reported in
`NanoP4Spec/Refinement.lean` as `-- no refinement theorem: X (reason)`.
Outside, for now: type parameters, function-typed parameters, externs,
calls of builtins (the port and the wrapper are not yet related by
lemmas), casts and subtype checks (`upcast`/`downcast`/`Match.sub`
against the generated bridges need per-type lemmas), iterated
expressions with a body and iterated premises, indexing, slicing, path
updates with indexing, membership, `else` groups (none in Nano-P4).

## Findings while driving the tactic

- `is_iter_var_exp` had a fuel of its own and answered `none` at zero,
  which sent the interpreter down the general iteration path instead of
  diverging: a low-fuel run could then succeed where the generated code
  takes another path. It now recurses on the expression's size (a
  `termination_by` through the phrase payload) and has no fuel.
- Long list literals elaborate into nested `have` chunks; a `decide` under
  a rewrite of a non-reducible definition makes simp's result ill-typed
  (so the `Q.*` constructors and `mkPhrase` are reducible); a named hole
  `?x` reused across two `cases` refers to the first goal of that name.

## Why not the alternatives

- Canon-equality, not an inductive similarity: one definition, one
  lemma (`eq_iff_canon`) to connect with the interpreter's comparison;
  exposure is a dozen small inversion lemmas. `canon` is not idempotent
  on `ExternV` (`Json.compress` is a `partial def`), which rules out a
  normal form `Value.eq (canon v) (canon w)`; the congruence
  `eq_of_canon` is used instead.
- The tactic does not re-run the code generator to name terms: the
  generated side supplies every term at the point it is consumed (call
  arguments, results, conditions), and facts are keyed by interpreter
  value variables, so no name resolution is needed.
- Per-definition `Holds` hypotheses would need the transitive callee
  set; one `HoldsSpec` over the whole quoted spec is uniform, and its
  membership proofs are cheap `List.Mem` terms.
