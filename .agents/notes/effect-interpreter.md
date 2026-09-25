# Shared interpreter effects checkpoint

2026-09-25, isolated branch `m3b-effect-interpreter`, based on `9bc0861`.
Implementation checkpoint, not an integration or full-P4 completion claim.

## Scope and compatibility

`Interp.Effects` parameterizes the existing evaluator over `Eval` or
`StateEval`. There is one recursive evaluator, not a second interpreter.
Context lookup, pattern assignment, and type/value helpers remain pure and
are lifted. Configuration and extern callbacks use the same carrier.
`eval_func` and `eval_rel` retain their pure interfaces; the default effect
instance also preserves existing unannotated pure call sites.

`evalFuncState` and `evalRelState` require an explicit initial counter and
return the counter on success, mismatch, and hard error. `init` only builds
tables: it does not establish or reset a session. Stateful fresh dispatch
checks type/value arity before allocating. Negation and rejected alternatives
retain effects, and shared rule premises are rerun for each attempted path.
Tracing observes the actual result once at the supplied state without
rerunning the computation. Its result-preservation equation has an immediate
exact axiom audit.

The refinement tactic now finds fuel by its explicit `Nat` binder rather
than by a fixed application argument offset. Three audited reduction
equations normalize the concrete pure effect operations. No existing
refinement statement, proof coverage, or axiom allowance was weakened.

The new AL fixtures exercise fresh success, signed wrap, failed retries,
hard-error stopping, all three terminating negation outcomes, shared
prefixes per attempt, output checking after allocation, extern effects,
explicit session continuation, and zero fuel. A higher-order callback passes
a defined allocator wrapper through local function resolution. A raw builtin
passed under a different local alias is not covered: existing dispatch uses
the local identifier for builtin selection. This stage does not change that
preexisting behavior.

## Recorded validation

All Lean and repository commands below ran in
`/Users/qobilidop/my/work/p4-spectec-lean-fresh-state` through
`nix develop /Users/qobilidop/my/work/p4-spectec-lean --command`.
The worktree has its own `.lake`; no original build directory was shared.

- `lake build --wfail P4SpecTec P4SpecTecTest.StateInterp NanoP4Spec`:
  **exit 0**, 116 jobs. This serial frozen-source run includes all existing
  Nano refinement proofs and their exact axiom audits.
- `lake build --wfail P4SpecTecTest.StateInterp`: **exit 0**. Includes the
  generic-carrier fuel-argument regression and unchanged pure call syntax.
- Focused `P4SpecTecTest.Print.Main` and
  `P4SpecTecTest.Diff.NanoP4Interp.Main` builds: **exit 0**.
- `lake build --wfail P4SpecTecTest`: **exit 0**, 130 jobs, after the
  verified Nano snapshot extraction described below.
- `scripts/check-imports.sh P4SpecTec P4SpecTecTest`: **exit 0**.
- `scripts/check-text.sh`: **exit 0**.
- `git diff --check`: **exit 0**.
- `python3 scripts/check-mirror.py`: **exit 1** because the isolated
  worktree's upstream submodule was not initialized. Importing that same
  script, setting only `UP` to the original pinned checkout's
  `upstream/p4-spectec/p4spec/lib`, and calling `main()`: **exit 0**.

An earlier overlapping pair of Lake builds failed on missing
`P4SpecTec/Refine/Calc.olean` for `find_action`. A dependency was being rebuilt
by the other process. That run is not counted as passing; the final serial
run above rebuilt `find_action` successfully. Initial development failures
in pure lifting normalization were fixed before the final build.

The first test-root build failed because the isolated worktree lacked the
ignored extracted `exports/nano-p4.al.json`. The checked-in snapshot was
verified and unpacked with `scripts/spec-snapshot.py unpack` (exit 0).

A scratch OCaml probe linked the actual pinned `Builtin.Fresh` and
`Interp_al.Backtrack` through the original flake's `#upstream` shell. Compile
and execution exited 0 after adding the required dynamic-runner archive to
the link command. Observed values/poststates, also checked in Lean:

| Operation | Outcome | Counter |
|---|---|---:|
| Invalid type arity from 7 | mismatch | 7 |
| Invalid value arity from 7 | mismatch | 7 |
| Valid call after those failures | `FRESH__7` | 8 |
| Allocate, mismatch, retry | `FRESH__1` | 2 |
| Allocate, hard error | hard error | 1 |
| Resume after that error | `FRESH__1` | 2 |
| Allocate at signed maximum | `FRESH__4611686018427387903` | -4611686018427387904 |
| Allocate after wrapping | `FRESH__-4611686018427387904` | -4611686018427387903 |

This is primitive/backtracking evidence, not a complete AL interpreter
differential oracle. The scratch source and executable are ignored local
artifacts. Durable upstream fixtures covering the complete AL programs,
especially negation, shared premises, and higher-order calls, remain to be
added during integration validation.

## Remaining obligations

Independent read-only review, integration with the concurrent byte-text
changes, the full local gate, and remote CI remain pending. Nothing has been
pushed from this worktree. No full gate was run or claimed here.

This stage supplies the interpreter carrier, not generator state selection,
stateful generated code, state-indexed rule propositions, or generated
stateful run-soundness/refinement proofs. Full-P4 support remains incomplete.
Execution is sequential and cache-free; mutable cache registration, hooks,
backtraces, and deterministic checking remain omitted. With fresh allocation,
checking extra alternatives can consume state, so those execution modes are
not claimed interchangeable. Existing fuel and type-checking boundaries are
unchanged. The parent integration should reconcile the human-facing design
deviation list with this explicit-state execution boundary.
