# Bounded shared verify port

2026-09-25. Isolated `m3d-nano-verify`, based on reviewed driver checkpoint
`2635a32`; the driver worktree remains frozen and untouched.

New partial mirrors: BackendSim.SpecImpl.Func (find_var_e/local only),
SpecImpl.Unpack (unpack_p4_bool only), Core.Func (verify only). NanoSwitch
function dispatch and ExternFunctionCall_eval route to that shared helper.
The original callback order, full-P4 prefixed-name/cursor ABI, result notes,
ctx/arch preservation and all StateEval outcomes remain explicit.
No static_assert implementation, typed PACKET repair, boot/STF port or
generated-file/upstream mutation is included.

The upstream Nano boundary is real and intentionally not repaired. Its
grammar admits extern objects only; its AL has ExternMethodCall_eval but
no ExternFunctionCall_eval. Its `find_var_e(scope, ctx, name)` differs from
the shared Core helper's `find_var_e(prefixedName, cursor, ctx)`. An actual
AL probe at both exact pins returns unmatch for that shared getter, and
Lean repeats the same mismatch with guard=false and unchanged counter.
That is an ABI rejection probe, not successful verify program coverage.

The direct original-target oracle has 19 observations, preserving typed
callback arguments/results. All match Lean, including ordered lookup,
malformed check values, false REJECT payload, true empty RETURN, exact
notes, errors and callback failure post-state. Five actual replay mutations
and seven offline contract tests pass. Divergence at either lookup remains
divergence. Details and exact reproduction: `test/nano-verify/README.md`.

Checks so far, all in pinned shells:

- Pipe build: exit 0, 46 jobs.
- Combined verify/target/driver/packet/NanoTarget focused build: exit 0,
  108 jobs, `.artifacts/verify-focused-build.log`.
- Nineteen-case upstream capture: exit 0; source/probe API corrections
  preceded the successful capture. Target's ARCH signature needed the
  existing Extern.Make wrapper for the independent interpreter probe.
- Initial AL Lean check incorrectly used default guard=true and failed;
  setting the observed guard=false explicitly restored exact mismatch.
- Seven offline contracts: exit 0. Final exact-pin recheck of all 19 cases
  and the explicit AL configuration/counter boundary: exit 0.
- Final direct Lean replay: exit 0, nineteen matches and five rejected
  mutations; actual Nano ABI mismatch and before/after counter 0 agree.
- Existing target check.py and eleven packet contracts: exit 0, including
  24 primitive/handler cases, eleven driver cases, six successful actual
  relation/driver events plus one guarded failure and existing mutations.
- Import completeness, diff-whitespace and explicit changed/new Lean widths
  and file-size checks: exit 0. Final verify executable rebuild after adding
  the observed boundary counters: exit 0, 98 jobs.

Independent root semantic/oracle review passes after resolving the spec
source-identity guard finding in both capture runners. Root reran nineteen
direct observations, the real AL boundary, five mutations, seven contracts
and six new spec-input guard regressions, all exit 0. Exact root/pin, clean
tracked files and absence of every untracked input (including ignored files)
are required; semantic fixture bytes are unchanged.

Narrow offline gate wiring is independently reviewed. It requires the new
files, runs both contract suites and builds/runs check-nano-verify. The
reviewer's 98-job build/replay and thirteen contracts exit 0. No upstream
capture or fetch is added to CI. Next: local checkpoint, reconcile published
main `1f5cfc0`, then combined full gate and final-head remote CI.
