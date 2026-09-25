# Fresh identifiers: audit and bounded foundation

2026-09-25. Upstream pin `8c8e0c6f`; full AL raw SHA-256
`803d798c13ae102e6aa970f65dfd2313d9d9b4094cae745049d3418c1af11953`.
The implementation experiment is on isolated branch `m3b-fresh-state`,
based on `7c1bfec`. No generator or interpreter integration is included.
The reviewed foundation is now integrated on `m3b-state-foundation`
above list-update commit `3b8175f`; the full local gate passed with no
skips. Independent review is in `.agents/reviews/m3b-fresh-state.md`.

## Upstream behavior

Paths below are relative to `upstream/p4-spectec/p4spec/lib/` unless a
`spec/` path is given.

- `interface/builtin/fresh.ml:8`: reject nonzero type/value argument
  counts before accessing the counter; format `FRESH__` plus the signed
  decimal old counter; increment; construct TextV; register through
  `add`; return the value. Registration is after increment.
- `interface/builtin/call.ml:27`: each `Builtin.Call.Make` instance owns
  one `int ref`, initially zero. `init` at line 31 resets it; checkpoint
  and seff at lines 35–36 only read/compare it. There is no restore API.
- Searching `p4spec/lib` and `p4spec/bin` found no invocation of builtin
  `init`. `interface/interface.ml:134` creates the P4 instance once.
  `Interface.P4.init` at line 155 only installs the printer. The runner
  initialization in `runner/make.ml:104` and `make_nonrec.ml:227` does
  not reset builtin state. Normal runner/spec reinitialization therefore
  preserves the counter; a fresh process/interface instance starts zero.
  Callers of our explicit interface must choose the session boundary,
  rather than resetting per function or program by accident.
- `interp/interp-al/backtrack.ml:46`: sequential choice evaluates
  alternatives in order. Ok stops; Err stops; Unmatch tries the next
  closure. None of these paths restores the mutable counter. A failing
  branch consumes IDs even when its local variable context is discarded.
- `interp/interp-al/interp.ml:1156`: a negative premise invokes its
  relation, flips Ok/Unmatch, and retains Err. Its allocations survive
  negation as well. Argument evaluation and iterated premises sequence
  their calls through the same global counter.
- `interp/interp-al/interp.ml:1320,1452`: successful relation/function
  invocations are memoized only when interface and external checkpoints
  report no side effects. These checks do not roll back state. An outer
  successful invocation detects effects of its failed alternatives too.
- `interp/interp-al/nondet.ml:28`: deterministic checking evaluates
  later alternatives even after a success. This can consume extra IDs.
  The current Lean sequential-mode boundary requires `det=false` for
  exact upstream comparisons; this foundation does not add deterministic
  checking, caches, hooks, registration, or failure traces.

## Overflow is real semantics

The pinned upstream shell has OCaml 5.5.0. On the project's 64-bit
platforms its `int` has 63 signed bits, range `[-2^62, 2^62 - 1]`.
The live OCaml probe printed:

```text
Sys.int_size = 63
max_int = 4611686018427387903
max_int + 1 = -4611686018427387904
min_int = -4611686018427387904
-1 + 1 = 0
```

Reproduce inside `nix develop /absolute/repo#upstream --command ocaml`
with `Printf.printf "%d %d %d %d\n" Sys.int_size max_int
(max_int + 1) min_int;;`. The recorded probe was noninteractive through
stdin. A 32-bit upstream build would have a different boundary and is
not claimed by the 63-bit foundation. An unbounded Nat counter would
match only under an explicit no-overflow restriction, not universally.

After a complete 2^63-step cycle a checkpoint equals its old value, so
upstream's side-effect detector itself cannot distinguish that cycle.
The foundation deliberately has no cache and claims no proof about
this pathological interaction.

## IDs are observable

- `spec/2-static-runtime/2.0-domain.watsup:34`: typeId aliases nameIR,
  ultimately text; `fresh_typeIds` repeatedly calls the builtin.
- `2.5.2-type-subst.watsup:54,71`: capture avoidance tests generated IDs
  for set membership and uses them as substitution keys and `_NAME`
  payloads. Identity is not merely diagnostic.
- `2.5.3-type-specialization.watsup:46,66,94,115`: implicit/omitted
  arguments receive fresh type IDs, returned in the instantiated types.
- `2.6-type-alpha.watsup:215`: alpha comparison allocates fresh IDs.
- `spec/5-typing/5.05.3-typing-type-argument.watsup:21`: a don't-care
  type argument introduces a fresh `_NAME`.
- `spec/7-instantiation/7.06-inst-statement.watsup:42–55`:
  DirectApplicationStmt_inst concatenates a fresh ID into emitted
  declaration and reference names.
- `spec/2-static-runtime/2.2.1-type.watsup:41`:
  `nameTypeIR = _NAME typeId hint(print %0)` prints that literal payload.
  The printer does not normalize `FRESH__n`; TextV printing preserves
  these ASCII bytes. `runtime/value/value.ml:44` compares TextV using
  `String.compare`, not alpha-equivalence.

Compare literal upstream output given the same initial state, call
sequence, evaluation order, and interpreter mode. Normalizing fresh
strings would hide mistakes and is not the current equality contract.

## Full-P4 effect graph

Recomputed from the gzip snapshot with Python in the Nix shell. The
scanner follows `Codegen/Exp.lean:callsOfDef`: function clause outputs
and premises; relation shared-match premises and path premises/outputs,
including the else group; table row outputs and premises. Traverse
expression children for CallE and premises for RulePr/IfHoldPr/
IfNotHoldPr, including iterated premises; ignore notes/hints. Compute
reverse reachability from fresh_typeId and SCCs on names of RelD,
FuncDecD, BuiltinDecD, and TableDecD, exactly the node set of Emit's
callable graph. Extern declarations are not SCC nodes.

| Set | Nodes including fresh builtin | Caller nodes excluding it | SCCs touched | Recursive SCCs | Multi-node SCCs |
|---|---:|---:|---:|---:|---:|
| All non-extern callables | 1,055 | — | 865 | — | — |
| Reverse closure of fresh_typeId | 262 | 261 | 139 | 23 | 8 |
| Also seed all higher-order definitions | 275 | 274 | 152 | 29 | 8 |

There are 1,060 callable declarations when the five externs are included.
The fresh closure contains 208 RelD, 53 FuncDecD, and the fresh BuiltinDecD.
The conservative closure contains 209 RelD, 65 FuncDecD, and that builtin.
Direct callers are exactly `fresh_typeIds`, `TypeArgument_ok`, and
`DirectApplicationStmt_inst`. Large affected groups include expression
evaluation (50), expression instantiation (30), statement typing (18),
argument typing (14), and substitution (7).

Seven definitions accept DefP:

```text
find_overloaded
find_overloadeds_named
find_overloadeds_unnamed
match_overloaded_named
match_overloaded_unnamed
reduce_serenum_binary
reduce_serenum_unary
```

The only unresolved static callee names are `check` and
`get_parameterListIR`, both function parameters. Sixteen definitions
pass DefA; the 28 distinct named global callback actuals are outside
the direct fresh closure. Two forwarded formal names are not global
functions. Thus all current closed-spec named callbacks are fresh-free,
but exported higher-order functions can accept an effectful callback.
Direct named-call closure alone is not a sound general effect analysis.

Seeding the seven higher-order definitions adds these thirteen nodes:

```text
Constructor_inst
find_callableDef_overloaded_e
find_callableDef_overloaded_t
find_constructorDef_e
find_constructorDef_i
find_constructorDef_overloaded_t
find_overloaded
find_overloadeds_named
find_overloadeds_unnamed
match_overloaded_named
match_overloaded_unnamed
reduce_serenum_binary
reduce_serenum_unary
```

Existing higher-order codegen is also a separate elaboration barrier:
`Codegen/Funcs.lean:54` and `Types.lean:68` form pure function-return
arrows, while `Exp.lean:444` qualifies a call's head globally even when
it should resolve to the local DefP binder. No higher-order support or
effect-closure correctness is claimed by the present experiment.

## Foundation implemented; architecture still open

`Prelude/StateEval.lean` defines FreshState as `BitVec 63`, with explicit
initial state, modulo seed conversion, signed observation, and wrapped
increment. StateEval is `ExceptT Fail (StateT FreshState Option)`:

```text
FreshState → Option (Except Fail α × FreshState)
```

The opposite transformer order, `StateT FreshState Eval`, would lose
post-state on failure. The foundation's choice retries only on Unmatch
with the first alternative's post-state. Negation retains post-state.
Lifting an existing Eval preserves the counter on success and failure;
divergence remains None. freshTypeId returns the old signed decimal
spelling and increments. It is a typed allocator primitive, not yet a
port of the value-level builtin's argument validation/registration.
Five small run equations have kernel proofs and exact axiom guards.
No axiom, sorry, opaque definition, or partial definition was added.

Do not silently replace current Eval or make fresh IDs a pure function
of ordinary arguments. An opaque mutable callback would move the
semantics outside the present pure proof boundary. Still open:

1. Add StateEval only to a conservative transitive effect closure, lift
   pure calls, and distinguish effectful callback signatures. This
   preserves pure surfaces but adds mixed-call and effect-analysis work.
2. Use uniform explicit state for the whole full-P4 library while
   retaining Nano's pure mode. This simplifies higher-order calls but
   changes more full-P4 function/proof signatures.

Before either integration, prototype the recursive Option-returning
carrier and its monotonicity/run-soundness rules. No partial_fixpoint
integration or stateful refinement theorem is delivered here. A future
refinement must relate initial and final counters for every terminating
outcome, errors/mismatches included, because enclosing choice observes
failed-branch effects. The old result-only Refines contract does not
implicitly establish this. Decide whether state-indexed Prop relations
or an explicitly weaker erased-state theorem are the intended API.

## Validation and remaining obligations

Commands ran with cwd `/Users/qobilidop/my/work/p4-spectec-lean-fresh-state`
under `nix develop /Users/qobilidop/my/work/p4-spectec-lean --command`.
The worktree has independent Lake build output and its own pinned
Batteries checkout; no shared/symlinked `.lake`.

- `lake build --wfail P4SpecTecTest.StateEval`: exit 0. Tests cover two
  allocations; mismatch/fallback; hard-error stopping and post-state;
  all three negation outcomes; nested calls and mapM, including a
  failing iteration; pure success/failure/divergence lifts; divergence
  suppressing fallback; explicit seed/resume/reset; negative counter;
  max-to-min signed wrap and seed modulo reduction.
- `lake build --wfail P4SpecTec P4SpecTecTest.StateEval`: exit 0,
  including all 65 core/focused build jobs and theorem axiom guards.
- `scripts/check-imports.sh P4SpecTec P4SpecTecTest`: exit 0.
- Live pinned OCaml counter-boundary observation: exit 0.
- Snapshot graph recount above reproduced 1,055/865, 262/139 and 275/152.

These focused checks alone did not complete the full repository gate or
independent review; both subsequently passed during integration (above).
Generator/interpreter integration and upstream builtin/backtracking
differential fixtures remain open. Existing Nano behavior is
not intentionally changed. This work is not a claim that full P4 now
generates, elaborates, or has stateful refinement proofs.
