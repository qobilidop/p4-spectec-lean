# Checked type runtime and separate fresh state

Compacted 2026-09-26. The bounded implementation was based on `b08ab8e`,
reviewed at `7a08bef`, and later integrated as `e31c1e8` (PR #21).
Durable interpreter-fidelity evidence with paused follow-ups, not corpus
coverage. Original notes
`type-runtime.md`, `type-fresh-reachability.md` and reviews
`m3c-type-runtime.md`, `m3c-type-runtime-reconcile.md` are recoverable at
Git `968ad65`. The summaries below preserve those reviews, not a fresh review.

## APIs and execution boundary

- `Type.Subst.Checked = ExceptT String Option`: success, error and fuel
  exhaustion are separate. Checked map creation validates arity and keeps
  the last duplicate binding, like upstream's `Map.add` fold.
- `Type.Expand.expand_typ` mirrors top-level PlainT alias expansion.
  `Type.Equiv` mirrors ordinary type, notation and bounded function
  equivalence; traversal preserves error-before-later-mismatch order.
- Checked `Value.Match` supports function values and propagates signature
  finder errors/exhaustion. Legacy Boolean APIs are retained unchanged.
- Checked `Typ.Make`/`DynamicAl.Func`/`Ctx` preserve nested-parameter
  exhaustion separately from a missing function. The interpreter uses
  them for value matching and required signature lookup.
- Guards, SubE, casts and type-argument substitution lift checked results:
  errors are hard `Fail.err`; exhausted recursion is `Eval.diverge`.
- Optional-iteration membership accepts a non-option value in its catch-all
  branch. Both checked and legacy matching preserve this unusual pinned
  upstream success (`runtime/value/match.ml:62–69`); it is not an omission
  to repair during cleanup.

## Explicit limits

Nonempty substitution through FuncT is rejected with an unsupported error;
the separate upstream Type.Fresh global counter is not modeled. Equivalence
uses private NUL-prefixed paired-binder markers before expanding aliases;
no marker escapes that Boolean result. It does not reproduce consumed
Type.Fresh increments for later observable substitution. The builtin fresh
counter is unrelated and unchanged. Claims concern well-formed parsed
identifiers; NUL-containing manually supplied identifier data and OCaml
physical-identity masking of malformed mixfix arguments are not covered.
The old pure helpers retain their recorded deviations, but are not used by
the migrated interpreter paths.

## Evidence

`test/type-runtime/probe.ml` records pinned upstream outcomes. The runner
requires the indexed pin, the exact committed four-file export patch,
no other dirty/untracked source, and a rebuilt full upstream main target
before linking. Scratch files are ignored; no source corpus is duplicated.
The fixture includes alias resolution, arity, unknown aliases, alpha
equivalence, free-alias/binder collision, higher-order errors, differing
returns, binder arity, evaluation order and duplicate-map behavior.
The duplicate-key alias is a directly constructed runtime diagnostic
fixture, not evidence that the parser accepts duplicate type parameters.

Lean TypeRuntime tests exercise those cases, explicit unsupported FuncT
substitution, empty-theta shortcut, signature/parameter exhaustion, SubE,
guarded callback values and hard-error/exhaustion lifting. Offline Python
tests mutate pin/root/patch/untracked provenance and require rebuilding
before linking.

The post-signature `lake build --wfail P4SpecTec P4SpecTecTest` passed all
153 jobs, including existing Nano refinement modules. The pinned oracle's
fourteen observations, three offline provenance tests, text and root-import
checks passed. Root independently reviewed the implementation and reran
TypeRuntime, the pinned fourteen cases and three offline tests (all exit 0),
with no remaining bounded findings (review detail below).
Offline CI wiring was independently reviewed with no findings and a passing
shell syntax check. The gate requires seven new paths and runs three offline
tests, not the optional real upstream oracle. Frozen
`nix develop --command bash scripts/check.sh` exited 0 with no skips after
PR 18 integration and this wiring. Both 78-case Nano differential legs and
48 output contexts, existing quotations/oracles/census passed. Actual
process exit was recorded. The historical report still owed remote CI;
that is not evidence of a failed current publication or of reviewer-run CI.
No full corpus replay or type-fresh fidelity is claimed.

## Separate Type.Fresh: pinned reachability assessment

The 2026-09-25 read-only assessment used upstream
`8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3` and verified full export SHA-256
`803d798c13ae102e6aa970f65dfd2313d9d9b4094cae745049d3418c1af11953`.
Recursive JSON traversal including notes counted 1,689 definitions, zero
FuncT tags and 3,917 CallE nodes with no FuncT type arguments. Seven DefP
nodes had empty own type-binder lists: the five overload lookup/matching
helpers and `reduce_serenum_unary`/`reduce_serenum_binary`. Of 101 DefA
references, thirty names comprised 28 monomorphic globals (eighteen tables,
ten parameter-list functions) plus forwarded `check`/`get_parameterListIR`.
Table parameter lists were not miscounted as type binders.

Runtime Typ/Value synthesize FuncT for callback notes, and `eval_arg`
constructs FuncV; assignment resolves its original declaration rather than
substituting those notes. Guard-disabled calls substitute static arguments;
casts substitute static aliases. No path from synthesized notes to those
inputs was identified. SubE/RecurseSC can invoke equivalence without guards,
but this export had no FuncT subcheck seed. This is an inspected static
argument, not formal reachability or protection against arbitrary external
function values.

Six scratch upstream processes observed Type.Fresh.tick before/after
Pass.algo, Backend_sim.Build.build, Interface.parse_program and eval_rel.
For both Program_ok and Program_inst on basic_routing-bmv2.p4, issue-212.p4
and issue-204.p4, all five phase counts were zero. Classes were pass/pass/
unmatch respectively; final builtin counters were 38/0/0. All processes
exited 0 using cache=true, det=false, guard=false, original paths, exact
pin/patch guards and rebuilt upstream libraries. Three compressed boot/result
artifacts also had zero FuncT tags. This is six bounded observations, not
corpus coverage; scratch artifacts are not durable recovery dependencies.
Reproduce by adding phase reads of `!(Runtime.Type.Fresh.tick)` to an ignored
copy of `test/p4-oracle/probe.ml`, without changing upstream or published schema.

General Type.Fresh names can escape: substituting Z↦Bool through a FuncT
with binder A, comparing X/Y signatures, then substituting again observed
`first=__FRESH0@1 equiv=true@2 second=__FRESH2@3`. Equivalence consumes a
separate hidden ID affecting later returned binders. `refresh` had no pinned
caller; this tick is not builtin fresh_typeId or parser Value.Fresh.
An alpha quotient for Boolean comparison is not exact typed-note transport.

A general port needs distinct signed-63-bit type-fresh state, retaining effects
through failure/retry and across calls, with explicit session initialization.
Do not merge it with the builtin counter or normalize returned names. Keep
observable nonempty FuncT substitution unsupported. The proposed tick sentinel
was subsequently implemented in the separate corpus-v2 schema, leaving the
published v1 API unchanged: five signed-range phases are validated, nonzero
ticks are unsupported, and malformed envelopes remain errors. Actual replay
mutations check this boundary. See [corpus](full-p4/corpus.md); a sentinel
detects excluded executions, it does not model Type.Fresh semantics.
Confidence high for census/observations, medium for inferred reachability.
Revisit on pin/export/census changes, external function types, guarded
higher-order coverage, a nonzero sentinel or enabling observable substitution.

## Review provenance and resolved findings

Independent root review compared checked Expand/Equiv/Subst/Typ/Func/Ctx/
Match and interpreter call sites with pinned OCaml. Fixed findings included
inner-before-iterator error order, structural mixfix traversal, substitution
arity, last-binding-wins maps, source/build provenance and nested-signature
exhaustion propagation. Private paired NUL-prefixed markers must be inserted
before alias expansion to protect free aliases colliding with binders.
They cannot escape Boolean equivalence; manually supplied NUL identifiers
and OCaml physical-identity masking of malformed values remain excluded.
Legacy total proof helpers remain separate from checked interpreter paths.

Root independently reran TypeRuntime, fourteen upstream observations and
three offline provenance tests, all exit 0. It did not repeat the author's
153-job build. Root separately reviewed offline gate wiring after `7a08bef`:
seven required paths, three unconditional tests, no real upstream/network
oracle in the ordinary gate; shell syntax passed. The author's full frozen
gate later passed exit 0/no skips, separately from review evidence.

An independent read-only agent reviewed reconciliation of main `e0d1bce`
into PR #21 head `268ac9860d44b4f3fc2fe4820b968e5695220d0c`. No source/gate
findings: type sources/tests stayed identical to `268ac98`, incoming proof/
replay code to MERGE_HEAD. A stale replay CI sentence was corrected to PR
#20 Gate `36209771264`, `0036247`, 4m44s and merge `e0d1bce`. Independent
offline tests (three type, six replay, twelve oracle) and shell syntax exited
0. That review did not rerun original semantics or claim final merged-head
CI/full gate. Current publication state belongs to root status.
