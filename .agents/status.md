# Status

Current checkpoint, updated 2026-09-26.

## Authorized scope

The user authorized continued N2 implementation after completing N0/N1.
N2 remains active; full Nano certification and broader full-P4 M3 are incomplete.
M3 stays paused. The [Nano plan and evidence](notes/nano-certification.md) owns
exit criteria, independent reviews, proof limits and measured costs.

## N2 implementation checkpoint

- Generated forward and reverse certificates now cover the same original 18
  functions on related inputs. Recursive reverse proofs use actual generated
  outcome induction and construct eventual reference executions, including
  failures. They do not assume forward determinism or global fuel monotonicity.
- All 26 builtins now have operation-specific dispatch equality and both
  invocation directions, with checked signature/carrier selection and exact
  type/axiom validation. Failed shape/arity decoding and operation failures
  have reusable family contracts. Printing retains the empty-hint requirement.
- Representation support separates independently defined source domains,
  admitted carriers, decoder soundness and sufficient fuel. Canonical ordering,
  normalization and legal equality dictionaries have audited reusable laws.
  These interfaces are not actual Nano source-domain/call-invariant bindings.
- Generated table initialization provides `HoldsSpec` and no local overrides.
  The field-update consumer uses this environment and the generated reverse
  theorem, removing over 500 lines of private proof duplication while preserving
  all public theorem statements. Its former private explicit fuel formula is
  no longer claimed; the public finite-execution guarantee is unchanged.
- Coverage is 350 declarations, 888 obligations, 139 compiled claim bindings
  and 749 unresolved: 18 forward, 18 reverse, 26 builtin dispatch and 77 relation
  run-soundness bindings. The additional builtin invocation certificates are
  checked without duplicating completion obligations. Bodied callers of builtins
  remain excluded until their call invariants and proof support are established.

## Validation and publication

Independent read-only reviews of the frozen implementations and integration
found no unresolved issue; the topic note preserves reviewer provenance,
reviewed hashes, later resolutions and limits. All 18 generated function groups
passed together with `--wfail` (41.680s). The production builtin sidecars and
exact coverage checker passed (10.804s), including thirteen distinguishing
mutations. Seventeen completion-adapter tests passed. The simplified consumer
certificate passed (497ms correspondence, 427ms certificate).

The full local gate passed with actual exit 0 (session 60774, 74.570s), all 44
stages and no skips. Evidence: `.artifacts/n2-full-gate.{log,json}`; tested index
tree `0f249ebf77ef66a2dbe66232b409a422526816a8`. This is a warm measurement,
not a controlled comparison with N1. Subsequent changes are checkpoint prose
only; executable inputs remain unchanged. Remote CI subsequently passed for published revision `c8f78f7`
([run 36294851006](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36294851006)).
N2 remains active; this is not milestone closure.
Strict core completion still rejects the inventory with actual exit 1 and the
expected incomplete-certification diagnostic (`.artifacts/n2-strict-core.log`).

## Current continuation (uncommitted, `n2-certification`)

Checked substitution now derives sufficient fuel from finite input syntax. Five
kernel-audited statements establish definitive results and stable type/list
results, including explicit errors. Every fixed-budget checked substitution
caller was migrated; legacy APIs and bounded recursive alias expansion remain
separate. Empty-substitution fast paths were preserved after independent review.
Focused `--wfail` validation passed for both runtime type test modules and
`Refine.Environment` (session 66512); the regression crosses depth 1,100.

Generated equality certificates passed for all 161 type declarations, including
noninjective polymorphic encoders. Initialized-table absence proofs and generated
Nano type-parameter freshness facts passed. Independent Sol review found no
issue in the equality/freshness implementation. The topic note records scope and
review limits. Source representation inventory/schema integration is in progress;
no additional completion binding is claimed before production codec validation.

Concurrent owned work continues on actual Type_eq/ParameterType_eq, polymorphic
in_set/dom_map iteration and the independent source grammar/recursive codecs.
A broader check exposed regressions in the actively edited reverse tactic;
restoring the original 18 certificates takes priority. The feature branch keeps
those experiments isolated from published main. No full gate has been run on
this evolving continuation and it has not been pushed.

## Next step and remaining N2 obligations

Complete the active proof/inventory integrations and independent reviews.
Establish actual source grammar/codec contracts for the four-member
`typeIR` representation SCC, with producer/cast and call-preservation proofs.
Complete Type_eq/ParameterType_eq, Type_ok and Var_init dependency closures.
Subtype/membership/iteration/type-argument support and reachable substitution
fuel obligations remain explicit. Legal polymorphic equality needs `ValueBEq`;
source tuple arities must not be confused with overlapping product dictionaries.
Source-valid values and runtime raw-extern values need separate recursive
admission predicates. No source-domain obligation has been removed from scope.

## Prior validated baseline and recovery

N1 closed at `56cf92c2201e25c11d1263cbdf6895a827afc612`, with successful
[CI 36290916636](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36290916636).
The preceding full local gate passed all 44 stages in 104.859s; its evidence
remains `.artifacts/n1-full-gate.{log,json}`. N1 includes recursive reverse,
relation, print and raw-extern feasibility evidence. Full target composition is
still N4; all 78 typing cases and 39 STF sessions remain in scope, with only
three STF sessions having stored upstream observations.

Organization, ordering and requested maintenance work are published; the
[maintenance evidence](notes/repository-stewardship.md) retains those reviews.
Build/test/CI optimization closed at `fd7ff9fd47aea72be1290b87e50be3ac1aa459d6`
with successful [CI 36286394307](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36286394307).
[Performance evidence](notes/ci-performance.md) preserves measured results.

The old N1 draft branch and temporary worktree were removed after successful
integration. One worktree remains. The older `docs/repository-review` branch
and local-only [archive backup](notes/archive.md) are preserved. The expected
four-file upstream exporter patch remains applied; no source pins changed.
