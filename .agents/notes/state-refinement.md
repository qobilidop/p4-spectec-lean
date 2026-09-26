# Bounded generated state refinement

Reviewed implementation `de73566` on `m3c-state-refinement`, base `dc1571b`.
PR integration branch `m3c-state-refinement-pr`, base `b08ab8e`, worktree
`/Users/qobilidop/my/work/p4-spectec-lean-state-refinement-pr`.

## Inherited interpreter boundary

The merged `Refine.StateInterp` checkpoint connects actual effect-parameterized
AL fresh dispatch and complete `invoke_func` to the typed byte-text allocator
for every fuel and initial counter, including signed wrap. Exhausted fuel is
divergence and imposes no obligation under the existing one-way contract.
Its hypotheses disable guards, select the builtin declaration through `Holds`,
and require an empty local function environment; the lower lookup theorem also
permits a matching local declaration. Raw builtin callback aliases are not
covered. Tracing is observationally transparent, and malformed builtin arity
mismatches before consuming state.

`StateRefinement` independently composes this boundary through both failures,
retry and negation, and rejects a state-resetting allocator even with a trivial
value relation. Its focused/full gates and independent review passed before
PR #16 merged; see `.agents/reviews/m3b-fresh-refinement.md`. Those handwritten
proofs are the boundary used here, not generated full-P4 refinement evidence.

## API and ownership

New modules only, plus their library-root imports:

- `Codegen.StateValidate.unsupported env externs d : Option String` selects
  the bounded syntax. The root production integrator owns Emit and must
  propagate exclusion reasons through dependencies, including recursive SCCs.
- `StateValidate.groupTheorems lib recursive members reasons : List Format`
  emits `.state_refines` declarations and audits, or explicit exclusions.
  The theorem quantifies over `Config StateEval`, arbitrary fuel and the usual
  guard/fenv/HoldsSpec hypotheses; `StateRefines` supplies arbitrary initial
  state and exact all-outcome final-state agreement.
- `Tactic.StateRefine` implements `state_refine_al`. Entry dispatch unfolds
  once; called functions use their existing `.state_refines` theorem. Missing
  contracts fail explicitly. Pure context/value normalization is reused without
  modifying `Tactic.Refine` or the interpreter.
- `Refine.StateNormalize` proves and immediately audits the state-preserving
  equations required by the driver. Right mismatch elimination keeps the
  consumed state; helper lifting distributes over pure bind only.

Fresh's emitted theorem applies `freshStateRefinesOfHolds` to the actual
quoted builtin declaration. No generated positive relation is introduced or
changed by this work, and no executable graph is substituted for one.

## Evidence

`P4SpecTecTest.StateValidate` invokes the actual function emitter and the new
theorem emitter on one quoted AL specification. Kernel-checked contracts
cover fresh, allocate, retry after consumed allocation, Bool selection, nested
calls, Nat aliases and return values, debug evaluation, final mismatch and
division-by-zero hard failure with a fallback that must not run. Every emitted
theorem passes `#audit_axioms`; the reusable normalization theorems have exact
`#guard_msgs in #print axioms` checks. Kernel-evaluated run observations confirm
the final counter on success, `.unmatch`, and `.err`.

Final pinned checks:

- `lake build --wfail P4SpecTec P4SpecTecTest.StateValidate`: exit 0, 78 jobs;
  fixture elaboration 37 seconds.
- `scripts/check-imports.sh`: exit 0.
- `scripts/check-text.sh`: exit 0.
- `git diff --check`: exit 0.

Root independently reviewed all new modules/tests and directly re-elaborated
the fixture in the frozen implementation tree (exit 0), finding no correctness
issues in this bounded contract. Review: `.agents/reviews/m3c-state-refinement.md`.
The independent PR branch's full pinned `scripts/check.sh` exited 0 with no
skips, including both Nano differential legs, quotations, print/text/state
oracles, transport sensitivity, and the full-P4 census. PR #19's initial
remote Gate passed on `c54e4eb` in 5m25s (run `36207315308`). The subsequent
merge of main `ea9533d` had only a status conflict, independently reviewed
by root with both requested documentation corrections applied. Refinement
source remains byte-identical to `c54e4eb`. The repeated frozen full gate
exited 0 with no skips, including the twelve incoming oracle contract tests:

```sh
nix develop /Users/qobilidop/my/work/p4-spectec-lean --command /Users/qobilidop/my/work/p4-spectec-lean-state-refinement-pr/scripts/check.sh
```

Final merged-head remote CI remains owed before landing.
Root is separately integrating and reviewing production generation;
it is not part of this PR. These results do not imply full-P4 elaboration or
refinement coverage.

## Remaining obligations

The initial fragment excludes recursion, relations, higher-order arguments,
type arguments, nonvariable patterns, compound types, general arithmetic and
all builtins other than fresh. The one numeric operation admitted is literal
Nat division, to exercise hard errors. This deliberately small eligibility
boundary must be broadened only with independently checked proof probes.

The shared normalizer runs repeatedly across fuel splits; these seven tiny
definitions take 37 seconds together. Measure full-P4 cost before claiming
scalability. The emitted fresh membership proof currently simplifies the
quoted spec list; larger spec representations may need the existing direct
membership-proof machinery. Recursive refinement will need a fuel induction
and modular group hypotheses; structural recursive run-soundness is a separate
completed checkpoint, not evidence that this driver handles recursive calls.
