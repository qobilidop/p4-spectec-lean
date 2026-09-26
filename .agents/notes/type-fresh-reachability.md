# Type.Fresh reachability at the full-P4 pin

Read-only assessment, 2026-09-25. P4-SpecTec pin
`8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3`; verified full AL snapshot SHA-256
`803d798c13ae102e6aa970f65dfd2313d9d9b4094cae745049d3418c1af11953`.
No production source or published oracle contract was changed. This guides
work order, not a formal reachability theorem or whole-corpus observation.

## Static method and results

Decode the checksum-verified `exports/p4.al.json` as JSON; recursively walk
every dictionary/list, including notes. Count lists tagged `FuncT`, phrase
nodes whose `it` is `CallE`, `DefP` and `DefA`, and inspect each CallE's type
arguments. Resolve concrete DefA identifiers through top-level definition
names; distinguish TableDecD parameter lists from function type-parameter
lists (table functions have no type parameters).

- 1,689 top-level definitions; zero FuncT tags anywhere, including notes.
- 3,917 CallE phrase nodes; no FuncT in any call type argument.
- Seven DefP nodes, all with empty own type-parameter binder lists:
  `match_overloaded_named`, `match_overloaded_unnamed`,
  `find_overloadeds_named`, `find_overloadeds_unnamed`, `find_overloaded`,
  `reduce_serenum_unary`, `reduce_serenum_binary`.
- 101 DefA references, thirty distinct names: twenty-eight concrete global
  callbacks (eighteen compatibility tables and ten parameter-list functions),
  all monomorphic; two forwarded local names, `check` and
  `get_parameterListIR`.

Relevant pinned source paths under `p4spec/lib/`:

- `runtime/type/typ.ml` synthesizes FuncT from DefP when converting a
  function signature; `runtime/value/value.ml` puts FuncT into FuncV notes.
- `interp/interp-al/interp.ml` `eval_arg` constructs those FuncV values.
  `assign_arg_def` resolves their identifiers to the original function
  record, rather than substituting or inspecting their note types.
- Guard-disabled `eval_call_exp` substitutes static type arguments;
  upcast/downcast substitute static plain aliases. No static FuncT seed or
  identified path from callback notes to these type inputs exists here.
- Function matching can call Type.Equiv even with guards disabled through
  SubE/RecurseSC, but this export has no FuncT subcheck seed. The synthesized
  callback signatures have empty own binders.

This is a static argument over the committed AL plus inspected call sites,
not a proof that arbitrary external values cannot inject a function type.
The next corpus replay should remain fail-closed on unsupported type-fresh
paths, rather than generalizing this argument beyond the pin.

## Six dynamic checks

An ignored scratch OCaml probe reused the reviewed full-P4 adapter's exact
source-pin/export-patch guard and compilation libraries. It read
`!(Runtime.Type.Fresh.tick)` before Pass.algo, after Pass.algo, after
Backend_sim.Build.build, after Interface.parse_program, and after
Interp.eval_rel. Each relation ran in a fresh process with cache=true,
det=false, guard=false, the pinned spec/include roots and original source
paths; no source corpus was copied. The real rebuilt primary upstream
checkout and the exact-pin ignored p4c checkout were referenced absolutely.
Compilation and all six subprocesses exited 0.

| Program | Relation | Upstream class | Type ticks (five phases) | Builtin final counter |
|---|---|---|---|---|
| basic_routing-bmv2.p4 | Program_ok | pass | 0/0/0/0/0 | 38 |
| basic_routing-bmv2.p4 | Program_inst | pass | 0/0/0/0/0 | 38 |
| issue-212.p4 | Program_ok | pass | 0/0/0/0/0 | 0 |
| issue-212.p4 | Program_inst | pass | 0/0/0/0/0 | 0 |
| issue-204.p4 | Program_ok | unmatch | 0/0/0/0/0 | 0 |
| issue-204.p4 | Program_inst | unmatch | 0/0/0/0/0 | 0 |

The three existing compressed boot/result artifacts also contained zero
FuncT tags. These observations are only these cases, not the corpus.
The instrumentation can be reproduced by adding phase reads to an ignored
copy of `test/p4-oracle/probe.ml`, not by changing upstream:

```ocaml
let tick () = !(Runtime.Type.Fresh.tick)
(* Read tick () before/after Pass.algo, Backend_sim.Build.build,
   Interface.parse_program and Interp.eval_rel; keep the original flags. *)
```

## Names can escape in the general runtime

`runtime/type/fresh.ml` owns a separate `tick = ref 0`. `fresh` returns the
current integer then increments it. Its `refresh` function has no caller in
the pinned p4spec source (a complete word search for `refresh` finds only
the definition; the parser refreshes Value.Fresh instead). It is neither
Interface.Builtin.Call.ctr nor the observed fresh_typeId counter.

A pinned scratch probe constructed a FuncT with binder A and nonempty
substitution Z ↦ Bool, then performed alpha-equivalence of X/Y function
signatures, then repeated the substitution. Exact output:

```text
first=__FRESH0@1 equiv=true@2 second=__FRESH2@3
```

The first/second names are the returned FuncT binder names; tick annotations
are the post-call separate counter. The Boolean equivalence call therefore
consumes an invisible ID that affects later returned type data. Nested tuple
or iterator cast notes and externally passed type arguments can expose such
data if those function-type paths are admitted. Exact typed-note JSON
comparison cannot assume an alpha quotient without a separate justification
and a changed observation contract.

## Minimal faithful general representation and order

A general port needs a distinct signed-63-bit type-fresh state, retaining
allocations across errors, rejected alternatives and evaluation calls, with
explicit process/session initialization. Equivalence must consume IDs too,
even though its marker names do not escape its Boolean result. Do not merge
this state with builtin fresh_typeId or roll it back on failure. An
alpha-quotient could be suitable for a proven narrower Boolean operation,
but is not an exact representation of observable returned type notes.

Prioritize streaming/sharded corpus replay at this pin, while checked
observable FuncT substitution remains an explicit unsupported error.
Consider a versioned upstream observation sentinel for type-fresh ticks;
bounded Lean replay should reject nonzero or changed type ticks until
modeled. That needs strict oracle/runner schema updates and counter-mutation
tests, not silent normalization or a change to the already published oracle.

Confidence: high in the static census, inspected call-site behavior and six
dynamic/synthetic observations; medium in the inferred guard-disabled
reachability boundary, which is not formal. Revisit on any pin/export bump,
a FuncT/type-binder census change, a nonzero sentinel, externally supplied
function types, guarded higher-order coverage, or enabling observable
function-type substitution.
