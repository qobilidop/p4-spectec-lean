# Shared verify and Nano dispatch observations

This bounded port mirrors `backend-sim/core/func.ml`'s `verify` and
`backend-sim/nano_switch/pipe.ml`'s function dispatch at P4-SpecTec
`8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3`. The new partial SpecImpl.Func
and SpecImpl.Unpack modules keep the pinned shared getter and Boolean
unpacking structure. All other shared helpers, static_assert, Nano boot,
STF parsing and typed target adapters remain outside this increment.

## The pinned Nano compatibility boundary

The original shared `Spec.Func.find_var_e_local` calls:

```
find_var_e [] [(_BARE nameIR):prefixedNameIR, LOCAL:cursor, ctx]
```

Nano's actual AL function instead expects `(scope, evalContext, nameIR)`.
The port does not adapt the shared ABI to Nano or repair that inconsistency.
The exact-pin AL probe records a mismatch when the original shared getter
calls Nano's actual `find_var_e`, in AL mode with cache/determinism/guard
disabled. Lean repeats that bounded call and also observes mismatch without
counter consumption. The supplied dummy context is not a booted program
context; this is an ABI boundary observation, not a valid verify execution.

More fundamentally, pinned Nano parser `externDeclaration` accepts only
`externObjectDeclaration` (`interface/nano/parser.mly`). Nano's
`8.01-eval-relation.watsup` has only `ExternMethodCall_eval`, and its callee
syntax has actions, extern methods and table apply methods, not extern
functions. The observed compiled AL confirms that sole extern relation.
No existing pinned Nano program or include declares/calls `verify`.
Therefore there is no real Nano verify packet/program coverage to claim.
Shared Core.Func behavior is directly covered for future v1model/eBPF work;
neither those architectures nor their packet paths are implemented here.

## What is compared

`observed.json` contains 19 fresh-process observations of original OCaml
Core.Func/target functions, with complete typed callback arguments and
outputs. True and false both look up `check` then `toSignal`, before unpacking
`_B bool`. True returns exactly `RETURN (None:value?) : returnResult`; false
returns `REJECT toSignal : rejectResult`. The signal is deliberately an
opaque raw errorValue extern, demonstrating upstream does not validate or
alter it. Context and architecture are returned unchanged.

The replay compares semantic values plus every nested type note. Regions,
value IDs and cache hashes are retained in the fixture but excluded from
comparison; no text or ExternV payload normalization occurs. Callbacks allocate
once each, so exact final counters also distinguish first/second lookup,
early failure and a mistakenly skipped second lookup. Cases cover bare,
wrong-tag and non-Boolean check values; callback abort/mismatch after either
lookup; malformed dispatch arguments, swapped parameters, static_assert,
unsupported lctk and unknown relation dispatch. Getter RuntimeError and
simulator abort are both Lean hard errors (not identical internal diagnostics);
callback mismatch remains distinct. Two Lean tests reject replacing first
or second callback divergence with a terminating outcome.

Five actual Lean replay mutations are rejected: final counter, lookup order,
callback ABI, result note and preserved context. Seven offline contract tests
cover exact pins/scope, request identity, shape/counters, explicit AL config,
and strict duplicate-key/nonfinite JSON rejection. The fixture read is bounded
at 1 MiB. These finite tests are not a universal target-correctness theorem.

## Reproduction

In the default pinned shell:

```
lake build --wfail check-nano-verify
python3 scripts/spec-snapshot.py unpack exports/nano-p4.al.json
python3 test/nano-verify/test_contract.py
.lake/build/bin/check-nano-verify
```

In the pinned upstream shell, with absolute exact-pin checkouts:

```
python3 test/nano-verify/run.py --upstream /absolute/p4-spectec \
  --spec /absolute/nano-p4-spec --check
```

The runner reuses the reviewed exact revision/export-patch guard and full
upstream rebuild before linking its probe. `--update` captures the durable
fixture; it is not permission to publish without review and a full gate.
Both capture runners now require the exact canonical spec repository root,
pinned HEAD, clean tracked files/index and absence of all untracked inputs,
including ignored files. Six disposable-repository tests cover these checks.
The offline gate builds/runs the verify replay and both contract suites;
it does not run upstream capture or fetch a repository. Existing real Nano
relation/driver packet replay is rerun as nonregression, not verify coverage.
