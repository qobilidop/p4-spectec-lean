# Stateful executable codegen checkpoint

2026-09-25, isolated `m3b-state-codegen` worktree, base `bf7fb62`.
This is executable-emitter implementation and compiled regression evidence,
not production full-P4 generation or stateful proof coverage. Root owns
the production guard in Emit/Validate and library imports; the separate
proof author owns structural Props/RunSound and optional-premise structure.

## Shared interface

- `Codegen.Mode.ExecMode`: `pure | freshState`. `Env.ofSpec` selects
  `freshState` only from a `BuiltinDecD` named `fresh_typeId`, never the
  generated library name, a user-defined function, or an effect closure.
- `Env.mode` defaults to pure for existing hand-built environments.
- `Attempt.RelAttempt` retains group/path identifiers, the complete
  group match, path premises and outputs. `Attempt.ofRelation` flattens
  in source order, with the else path last. `Rels.attemptBlock` compiles
  exactly that attempt to `List Stmt × List Term`; `attemptTerm` uses
  the same block. Stateful relations repeat the shared prefix on retry.
- Existing statement constructors and pure render helpers are preserved.
  `Stmt.renderWith mode`, `doOfWith mode`, `doOfMWith mode` thread the
  carrier through nested blocks. The proof author's shared `.optM` node
  now retains optional-premise element binders, body statements, both
  results and source options. Only stateful optional premises use it;
  pure output remains unchanged. The pure Props translator has an explicit
  rejection case until the stateful consumer is integrated. An opaque
  `.bind` alone cannot justify structural positive relation premises
  hidden inside optional iteration.
- Generated definitions have an explicit final `(state : FreshState)`
  parameter in stateful mode, and `StateEval.run body state` returns
  `Option (Except Fail Result × FreshState)`. Internal calls remain
  `ExceptT.mk (callee args)`; no call invents or resets a state.

## Implementation boundaries

Functions, relations, tables, builtin wrappers, extern fields and recursive
callback signatures use the same selected ABI. Pure helpers remain pure
and are lifted via `StateEval.liftEval`; negative premises use
`StateEval.notHold`. The fresh wrapper checks declaration arity and the
resolved text result, then encodes the allocator's ASCII String as ByteText.
It rejects fresh emission in pure mode. It does not fabricate function
values or ToValue instances for arbitrary Lean functions.

Clause/table DefA binders establish lexical callback names. Calls and
forwarded DefA arguments resolve local names before global/extern names.
`paramTypes` recursively preserves nested callable signatures instead of
erasing nested DefP structure. Rank-polymorphic callbacks are explicitly
rejected by `validateCallableType`; `validateSignatures` covers extern
declarations too and must be invoked before production rendering.
Root's initial review found a signature-only validation gap: named type
aliases could hide rank-polymorphic function types. Validation now scans
every Plain/Struct/Variant type body directly and rejects function-valued
data, including functions inside tuples/lists/type arguments, for which no
faithful codec exists. This finite scan does not unfold recursive aliases.
Hidden polymorphic and list-of-functions aliases have rejection guards.
The ordinary type renderer assumes this validation; it is not a second
validation entry point.

`callsOfDef` retains its public signature but collects global DefA edges
and filters locally bound callback references. Emit's existing dependency
graph thereby includes callback-only cycles and extern requirements.
DebugPr compiles/evaluates its expression even though printing is omitted.
Two optional-expression defects surfaced in actual emitted-code tests:
zero bound variables discarded effect statements, and one bound variable
emitted a redundant catch-all. Both are fixed; neither changes Nano output.

## Checked evidence

Commands use `nix develop /Users/qobilidop/my/work/p4-spectec-lean
--command ...` with explicit byte-worktree cwd. No full gate or remote CI
has been run for this slice; no commit or push performed by this author.

- `lake build --wfail P4SpecTec.Codegen.Rels`: exit 0, 26 jobs.
- `lake build --wfail P4SpecTecTest.StateCodegen`: exit 0, 47 jobs after
  final executable changes. Tests parse and elaborate real emitted source,
  then execute it: signed wrapping allocation, repeated shared-prefix retry,
  DebugPr allocation/hard error, distinguishable negative branches,
  named/forwarded/nested callbacks, local shadowing of a global or extern,
  stateful extern-function mismatch and extern-relation success, ordered
  list expressions/premises, optional zero/some/none cases, mixed optional
  inputs producing hard error without effects, table retry, and recursive
  partial_fixpoint traversal.
  Separate emitted pure callbacks also execute successfully.
- The same fixture invokes the real planner in pure mode: callback-only
  dependency cycles form one mutual group, and an extern passed only as
  DefA propagates the Externs requirement. Stateful production planning
  stays rejected. Malformed fresh signatures and nested polymorphic extern
  callbacks fail validation.
- `lake build --wfail p4spectec-gen`: exit 0, 66 jobs. Existing macOS linker
  deployment-version warnings remain toolchain diagnostics, not Lean warnings.
- `lake exe p4spectec-gen exports/nano-p4.al.json --lib NanoP4Spec --check`:
  exit 0, all 48 files up to date.
  Rebuilt the executable and repeated its direct `--check` invocation after
  final `.optM` integration: exit 0, all 48 files still up to date.
- `git diff --check`: exit 0. New Lean files checked separately for the
  100-character width limit because the repository text script only visits
  tracked files.
- `lake build --wfail P4SpecTecTest.StateCodegen P4SpecTecTest.Updates
  P4SpecTecTest.Text.Main`: exit 0, 65 jobs. The subsequent alias-validation
  correction also passed the 47-job StateCodegen target. Final rerun after
  `.optM` integration, optional-premise fixtures and extern-relation test:
  exit 0, 65 jobs.
- `scripts/check-text.sh`: exit 0 for tracked files.
- `scripts/check-imports.sh`: exit 0.

Early test/build drafts failed on ambiguous AL/IL type names, a wrong
optyp constructor, missing Except.isError, and the optional wildcard above;
these are resolved. The recursive fixture was corrected to use an explicit
empty-list guard: a refutable input pattern is a hard error upstream, not
a clause-selection mismatch.

## Review corrections, recovered 2026-09-25

All three findings in `.agents/reviews/m3b-state-codegen.md` have targeted
corrections and emitted-code regressions:

- Optional expressions use the pure `Option.map` shortcut only with one
  input. Multiple inputs always match all-some/all-none/mixed and raise
  `Fail.err` for mixed optionality. Pure and stateful compiled fixtures
  execute both mixed orders, all-present and all-absent.
- Signature validation retains `ExpP`/`DefP` provenance. Data parameters,
  results (including callback results), and relation arguments reject
  direct `FuncT`, as well as the prior alias/container checks. Actual
  nested `DefP` parameters retain their recursive callback ABI.
- Recursive emission names already-defined callback consumers which
  `codegen_monotonicity` may expose. It never assumes an extern or
  arbitrary callback is monotone. The tactic uses ordinary monotonicity
  composition plus kernel-proved fixed-point lemmas: pointwise chain
  suprema preserve callback monotonicity, and the body invariant lifts
  through least-fixed-point induction. Actual pure and stateful generated
  mutual cycles now elaborate and execute, including a callback passed
  through an already-recursive consumer. Their axiom sets are exactly
  `propext`, `Classical.choice`, `Quot.sound`. Consumer discovery is
  skipped for nonrecursive definitions and reaches a finite closure.

The recovery's first focused build exited 1: the surviving partial
monotonicity fix could not handle the recursive consumer. The first
invariant-tactic drafts also failed (including an unconstrained
application fallback, fixed by inspecting the application before applying
its theorem, and an omitted local monotonicity hypothesis). Two runaway
draft build processes were terminated. These were development failures,
not gate evidence; no failing draft was committed or pushed.

Raw builtin/extern callback aliases are deliberately rejected at global
`DefA` sites in both modes. Pinned upstream `interp.ml:326–332` copies
the declaration under the local binder; `invoke_func_body:1480–1486`
passes that local identifier to builtin/extern dispatch at 1493–1514.
A Lean closure capturing the original global dispatcher name would
therefore silently change semantics. A defined wrapper is supported:
its body still calls the original global name. Local callback forwarding
and local names shadowing global/extern declarations remain supported.
Tests reject raw aliases, compile the wrapper case and retain dependency
edges needed for Externs propagation. No claim of faithful arbitrary
external callback invocation or guarded higher-order refinement follows.

Recovery verification (same explicit Nix shell/workdir as above):

- `lake build --wfail P4SpecTecTest.StateCodegen P4SpecTecTest.Updates
  P4SpecTecTest.Text.Main p4spectec-gen`: exit 0, 101 jobs.
- Built `p4spectec-gen exports/nano-p4.al.json --lib NanoP4Spec --check`:
  exit 0, all 48 files byte-identical.
- After the finite-closure optimization and stricter callable-result
  helper: `lake build --wfail P4SpecTecTest.StateCodegen p4spectec-gen`,
  exit 0, 83 jobs; generator check repeated, exit 0, all 48 files current.
- `git diff --check`, `scripts/check-text.sh`,
  `scripts/check-imports.sh`, and an explicit width scan of the four new
  Lean files: exit 0.

Root independently inspected and approved inclusion of the inherited
integration edits: `Emit` retains the production stateful guard, invokes
signature validation and conditionally imports the monotonicity tactic;
`Validate` keeps stateful refinement rejected and rejects callback tables;
the pure `Props` path rejects stateful input and opaque optional premises;
library roots import the new modules and regression fixtures.

The full local gate, remote CI and full-P4 generation were not run for
this isolated executable slice. Follow-up independent review is required.
Root retains production stateful guards until structural Props and
run-soundness are integrated; stateful refinement remains a separate
obligation. The emitted fixtures establish the tested callback shapes;
other recursive higher-order forms must discharge their own monotonicity
proofs or fail elaboration, never receive an assumed contract.
