# Stateful interpreter oracle

`run.py` compiles `probe.ml` against the indexed P4-SpecTec submodule and
records actual OCaml results in `observed.json`. It refuses a checkout whose
HEAD differs from the indexed gitlink. `--check` rebuilds the probe and
requires the committed fixture to be byte-identical. An initialized, built
submodule is required; an isolated worktree may pass `--upstream` with an
absolute path to another checkout at the same commit.

Ten cases execute a small AL spec through upstream's real
`Interp_al.Interp.Make` functor with `Interface.SpecTec_AL`: allocation,
rejected alternative, hard-error stopping, three negation outcomes with
distinct first/fallback result tags, repeated shared premise, higher-order
callback, extern-triggered retry, and session continuation after failure.
Five more cases directly invoke upstream `Builtin.Fresh.fresh_typeId`,
including type/value arity rejection and signed OCaml-int wrap. The `scope`
field distinguishes these primitive observations from complete AL execution.

The complete-AL cases run with caches, deterministic checking and input/output
guards disabled (`cache=false`, `det=false`, `guard=false`). They test the
sequential evaluator, not guarded higher-order compatibility or other modes.

Upstream's public `eval_func`/`eval_rel` results collapse internal hard
errors and mismatches to `Run.Fail (Unmatch _)`; the fixture therefore tests
observable success/failure, text payload and exact post-state, not an
unobservable internal failure tag. Lean's separate `StateInterp` guards test
its `.err`/`.unmatch` distinction. Signed-wrap, arity rejection, output
checking after allocation and zero fuel are not full-AL oracle cases:
the first needs a public counter seed setter, arity belongs to direct builtin
dispatch, output checking depends on a deliberately mismatched signature,
and upstream's interpreter is not fuel-indexed. The last two remain Lean-only
checks. This fixture is not a full-P4 differential oracle.
