# Stateful AL oracle checkpoint

2026-09-25, isolated branch `m3b-state-oracle` based on `a81265d`.
This is a focused differential oracle, not full-P4 generation evidence.

`test/state/run.py` compiles the actual pinned OCaml
`Interp_al.Interp.Make(Interface.SpecTec_AL)(Extern)` and a small AL AST.
It checks the indexed submodule gitlink against the actual upstream HEAD,
rejects a path that is not a repository root, and writes reproducible
observations to `test/state/observed.json`. A direct primitive group calls
the actual `Builtin.Fresh.fresh_typeId`; its `scope` is explicitly different
from complete AL execution. The Lean executable reads the fixture at
runtime, repeats the gitlink/HEAD/revision guard, requires the exact case
list, and compares the port's payload and post-state to upstream.

The 15 observations comprise ten full AL/session cases and five primitive
ones. Full AL covers fresh allocation, failed retry, hard-failure stopping,
three negation outcomes with distinct first/fallback text tags, a shared
premise rerun, higher-order callback, extern-triggered retry, and explicit
continuation after failure. Primitive cases cover valid allocation, type
and value arity rejection, and both sides of signed OCaml-int wrap. All
counter values come from the upstream interface's actual checkpoint or
the direct fresh counter, not inferred from a Lean result.

Complete AL observations explicitly use `cache=false`, `det=false` and
`guard=false`. In particular, the callback case does not establish guarded
function-value matching or equivalence to cached/deterministic execution.

The upstream public `eval_func` and `eval_rel` entrypoints collapse internal
`Err` and `Unmatch` into `Run.Fail (Unmatch _)`, so this fixture compares
observable success/failure and exact state, not an internal failure class.
For direct primitive cases, the probe catches only upstream `BuiltinError`,
and the Lean consumer requires exactly `.unmatch`, never `.err`.
The existing `P4SpecTecTest/StateInterp.lean` checks Lean's `.err` and
`.unmatch` distinction separately. Signed wrap and arity errors are direct
builtin cases, not complete AL cases. Output checking after allocation and
zero-fuel behavior remain Lean-only checks; upstream has no fuel index.
This oracle does not cover generated stateful code, proof obligations, or
the full P4 spec.

Focused commands (isolated worktree `/Users/qobilidop/my/work/p4-spectec-lean-state-oracle`):

- `nix develop /Users/qobilidop/my/work/p4-spectec-lean#upstream --command python3 /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/test/state/run.py --check --upstream /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec`: exit 0.
- `nix develop /Users/qobilidop/my/work/p4-spectec-lean-state-oracle --command lake build --wfail check-state-oracle`: exit 0.
- `nix develop /Users/qobilidop/my/work/p4-spectec-lean-state-oracle --command /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/.lake/build/bin/check-state-oracle --upstream /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec`: exit 0, all 15 cases.

No full gate, push, or integration claim at this checkpoint.
