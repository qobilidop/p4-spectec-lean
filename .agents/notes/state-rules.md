# Ordered structural state premises

2026-09-25. Bounded proof fixture in `P4SpecTecTest/StateRules.lean`,
authored in isolated `m3b-state-props` from `bf7fb62`. No production
stateful generation or proof automation is enabled by this checkpoint.

## Result and representation constraint

`StateChain P` records one structural `P` premise per element, linking
its initial/final state to its neighbors. Unlike `MapSteps`, its premise
is not restricted to an executable equation. The fixture's `Visits.node`
requires both a rejected-prefix witness and `StateChain Visits` for two
ordered recursive children. `Visits.leaf` describes literal fresh-name
production. Neither constructor is a definition of `Visits` as its run
graph.

Lean accepts this recursive occurrence:

```lean
StateChain Visits [n, n] u xss t
```

It rejects the superficially equivalent captured predicate:

```lean
StateChain (fun (_ : Unit) u xs v => Visits n u xs v) [(), ()] u xss t
```

The kernel reports that nested-inductive parameters cannot contain local
variables (`n` in this example). A `#guard_msgs` negative regression
preserves this exact boundary. General iteration codegen must therefore
make enclosing context explicit in the chain inputs or emit auxiliary
mutual step relations with that context as indices. Simply putting the
old pointwise translation into a stateful lambda is insufficient.

## Soundness experiment

The executable `visits` first runs a complete rejected attempt: allocate,
recursively visit a smaller input, then mismatch. Its selected branch
either allocates a leaf or uses `mapM` for two recursive children. Failure
does not roll back the rejected allocation or the recursive child's state.

`visitsSound` uses `partial_correctness` with an all-outcome realization
component and a structural successful-result component. Realization
transports the recursive approximant's rejected computation to the final
definition before constructing `RejectedPrefix`. Successful `mapM`
supplies `MapSteps`; `chainOfMapSteps` uses the recursive structural
induction hypothesis at each step to produce `StateChain Visits`.
Keeping the graph witness alone would not prove this constructor.

Four executable guards check exact outcomes and final counters:

| Run from zero | Outcome | Final counter |
|---|---|---:|
| `visits 0` | `[FRESH__1]` | 2 |
| `visits 1` | `[FRESH__4, FRESH__6]` | 7 |
| `visits 2` | `[FRESH__12, FRESH__14, FRESH__19, FRESH__21]` | 22 |
| `rejected visits 2` | mismatch | 8 |

All named theorems and the recursive executable have exact axiom guards.
`visitsSound` uses only `propext`, `Classical.choice`, and `Quot.sound`.
The fixture does not claim a reachable hard-error execution, general
ordered-attempt automation, or a translation for arbitrary iterated AL
premises. The rejected attempt has a separately proved no-success property.

## Recorded checks and integration

Commands ran in `/Users/qobilidop/my/work/p4-spectec-lean-state-props`
through `nix develop /Users/qobilidop/my/work/p4-spectec-lean --command`,
using an independent `.lake` directory.

- `lake build --wfail P4SpecTec.Refine.StateCalc`: exit 0.
- `lake build --wfail P4SpecTecTest.StateRules`: exit 0, including four
  execution guards, exact theorem audits, and the negative kernel test.
- `scripts/check-imports.sh P4SpecTecTest`: exit 0.
- `scripts/check-text.sh`: exit 0.
- `git diff --check`: exit 0.

An initial captured-predicate experiment failed as recorded above.
Placing recursive calls behind helper abbreviations also initially blocked
monotonicity synthesis; spelling out the recursive body, as generated
executables do, compiled with the existing StateEval monotonicity lemmas.
Intermediate proof-elaboration failures were corrected and are not counted
as passing checks.

The worktree also contains uncommitted executable-codegen dependency
snapshots (Mode, Attempt, Env, Types, Exp, Funcs, Rels) authored by the
separate executable workstream. Those are deliberately excluded from this
checkpoint. They are not needed to build this fixture. No full gate,
upstream differential check, remote CI, or push is claimed here.

Next: structural stateful Prop emission and run-soundness, using the shared
complete-attempt compiler. Production state generation and standalone
state Prop emission remain fail-closed until that integration is proved.
