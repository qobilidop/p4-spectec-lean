# Independent executable state-codegen review

2026-09-25. Reviewed the frozen uncommitted changes on
`m3b-state-codegen`, HEAD `bf7fb62f10ecee69ede41724b898272c15ea08ae`, in
`/Users/qobilidop/my/work/p4-spectec-lean-byte-text`. Read the repository
instructions, status, decisions, design, Lean pitfalls, author checkpoint,
and the root worktree's state-integration plan. This is an independent
read-only implementation review; only this report was written. No source,
fixture, author note, commit, or push was changed.

## Findings

No high findings. Three medium findings need correction before integration.

### Medium: pure optional-expression bodies suppress optionality errors

`P4SpecTec/Codegen/Exp.lean:543–548` takes the `stmts.isEmpty` shortcut
for an optional expression with multiple bound variables. It emits a
sequence of `Option` binds. Mixed `some`/`none` inputs therefore produce
a successful `none`, whereas upstream requires a hard error. The adjacent
effectful-body branch correctly checks all-some/all-none/mixed inputs.

This is an existing pure shortcut newly reused by the stateful emitter,
not a defect in the new `Stmt.optM` optional-premise renderer. The
`optionalMixed` regression exercises an optional **premise** containing a
fresh call and does not cover an optional **expression** with a pure body.
The mismatch can also permit subsequent allocations that upstream would
never execute after the hard error.

Exact reference: pinned upstream
`p4spec/lib/interp/interp-al/ctx.ml:290–310`, `sub_opt`, requires all
inputs to agree on optionality and otherwise calls `back_err`;
`interp.ml:1040–1050`, `eval_iter_exp_opt`, propagates that result. The
Lean `Ctx.sub_opt` implements the same check at lines 273–285.

Reproduction used `lake env lean --stdin` in the Nix shell and parsed and
elaborated the real `Funcs.funcDecl` result. Its AL clause has two inputs,
`a?` and `b?` (the ordinary `IterE (VarE ...)` input patterns), and output
`IterE (NumE (Nat 3)) (Opt, [a, b])`. `Env.mode = freshState`. The exact
emitted definition was:

```lean
def «$mixed» (p0 : Option Nat) (p1 : Option Nat) (state : FreshState)
    : Option (Except Fail (Option Nat) × FreshState) :=
  StateEval.run
    (do
       have a? := p0
       have b? := p1
       pure (do
          let a ← a?
          let b ← b?
          pure (3 : Nat))) state
```

`#eval «$mixed» (some 1) none 5` returned
`some (Except.ok none, 0x0000000000000005#63)`; probe exit 0.
Expected: `some (.error .err, 5)`.

Required correction: preserve the upstream mixed-input error even when
the body has no hoisted statements; add an emitted-and-executed regression
for both mixed orders, all-present, and all-absent expression inputs.

### Medium: callback-only recursive SCCs emit non-elaborating code

`Exp.callsOfDef` now correctly discovers global `DefA` edges, but the
resulting recursive code needs higher-order monotonicity support.
`Funcs.runBodyWith` appends `partial_fixpoint` without providing that
support. Passing a recursively defined function as an argument to a
previously generated callback consumer is not accepted by Lean's
monotonicity tactic merely because both recursive definitions are in one
mutual block.

The dependency regression at `P4SpecTecTest/StateCodegen.lean:140–146`
checks emitted text for `mutual`, `source`, and `later`. It does not
elaborate the discovered cycle. The separately elaborated `drain`
regression has direct recursion and does not exercise this boundary.

Reproduction again used `lake env lean --stdin`, invoking `Funcs.funcDecl`
on these AL definitions, parsing and elaborating the returned source:

- `through` binds a zero-argument text callback `f` and returns `f()`.
- `source` returns `through(DefA later)`.
- `later` returns `through(DefA source)`.

The environment was stateful. `through` was emitted nonrecursive;
`source` and `later` were emitted with `recursive = true` and joined with
the actual `mutualBlock` helper. This is the callback-cycle shape already
used in the dependency regression. The relevant emitted body is:

```lean
def «$source» (state : FreshState)
    : Option (Except Fail P4SpecTec.ByteText × FreshState) :=
  StateEval.run
    (do
       let tmp_0 ← ExceptT.mk (ReviewCycle.«$through» ReviewCycle.«$later»)
       pure tmp_0) state
  partial_fixpoint
```

The probe exited 1 with:

```text
Could not prove 'ReviewCycle.«$source»' to be monotone in its recursive calls:
  Cannot eliminate recursive call `ReviewCycle.«$later»` enclosed in
    «$through» «$later»
```

Required correction: make the generated higher-order recursion acceptable
to `partial_fixpoint` (with justified monotonicity support), and elaborate
the actual emitted callback-only recursive group in a regression. SCC
discovery is necessary but insufficient. This is executable compilation
failure, not a deferred stateful run-soundness/refinement proof obligation.

### Medium: direct function-valued data bypasses signature validation

`Funcs.validateSignatures` maps `paramTypes` over parameters and then calls
`validateCallableType` on every resulting type and the function result.
This erases the distinction between a `DefP` callback binding and an
`ExpP` data parameter whose type happens to be `FuncT`. The latter, and
direct `FuncT` results, pass validation despite the explicit rejection of
function-valued data hidden in aliases/containers. Nested callback
parameters are different: those have an actual `DefP` binder and are the
intended supported higher-order ABI.

An executable stdin probe constructed this pure AL declaration:

```lean
private def ft : typ' := .FuncT [] [] (Q.t .TextT)
private def d : Lang.Al.def := Q.d (.FuncDecD (Q.i "functionDataIdentity") []
  [Q.pm (.ExpP (Q.t ft))] (Q.t ft)
  [Q.cl [Q.ar (.ExpA (Q.e (.VarE (Q.i "x")) ft))]
    (Q.e (.VarE (Q.i "x")) ft) []] none [])
```

With `env := Env.ofSpec "FunctionDataProbe" [d]`, the actual results were:

```text
Funcs.validateSignatures env: Except.ok ()
Validate.unsupported env [] d: none
Emit.plan env [d] summary: refinement theorems: 1 of 1 definitions
```

The generated theorem includes these binders:

```lean
(p0 : (Option (Except Fail P4SpecTec.ByteText)))
(h0 : Rel v0 p0)
```

The zero-argument callable type renders as its result ABI. No faithful
`ToValue` instance exists for that ABI. A second stdin probe of exactly
`Rel v p` at this generated type exited 1 with
`failed to synthesize ToValue (Option (Except Fail ByteText))`.
This is not an arbitrary type alias rejection request: production pure
planning currently admits this direct data signature and classifies its
refinement as supported. Function-returning signatures need the same
explicit treatment rather than being admitted merely because Lean can
represent functions.

Required correction: retain parameter provenance during validation;
validate `ExpP` and callable results as data, and recurse through actual
`DefP` callback argument structures. Reject direct function-valued data
unless a supported value representation and correspondence are supplied.
Add direct `ExpP FuncT` and `FuncT` result regressions alongside the
existing alias-hidden cases.

## Positive checks and limits

- Complete stateful relation attempts repeat input matching and shared
  premises per path, in source order with the else path last. This matches
  pinned upstream `interp.ml:1362–1410`.
- State is passed through the uniform callable/callback/extern ABI;
  internal calls do not reset it. Pure failing helpers are explicitly
  lifted. Negation uses `StateEval.notHold`, retaining post-state.
- Lexical callback resolution precedes global/extern resolution. DefA
  references are included in dependency collection, with local bindings
  excluded. Alias-hidden function data and rank-polymorphic callbacks
  receive explicit signature validation failures.
- `DebugPr` now compiles its expression, retaining effects and failures.
- Production stateful planning, pure Prop generation on stateful input,
  and stateful refinement remain explicitly rejected. This review does
  not request removing those guards before the structural proof work.

All commands ran with explicit workdir
`/Users/qobilidop/my/work/p4-spectec-lean-byte-text`, prefixed by
`nix --no-warn-dirty develop /Users/qobilidop/my/work/p4-spectec-lean --command`:

- `lake build --wfail P4SpecTecTest.StateCodegen P4SpecTecTest.Updates
  P4SpecTecTest.Text.Main`: exit 0, 65 jobs.
- Both generated-code stdin probes above: optional-expression probe
  exit 0 with the incorrect successful result; callback-cycle probe
  exit 1 with the exact elaboration failure above.
- Direct function-data validation/planning probe: exit 0, incorrectly
  admitted and marked 1/1 refinement coverage. Its emitted `Rel` binder
  instance-check probe: exit 1 with the missing codec instance above.
- The built generator invoked by absolute executable path with
  `exports/nano-p4.al.json --lib NanoP4Spec --check`: exit 0, all 48 files
  up to date. An initial invocation used an absolute export argument and
  reported 48 stale files (exit 1), because that argument is embedded in
  generated source headers; rerunning with the canonical export argument
  passed. No output files were written.
- `git diff --check`: exit 0.

The full gate, remote CI, full-P4 generation, stateful structural proofs,
and new upstream oracle runs were not performed by this reviewer. Focused
tests establish the listed executable cases, not guarded higher-order
interpreter fidelity or complete stateful generation.
