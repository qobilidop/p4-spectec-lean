# Bounded field-update certificate review

Independent review by `/root/p4_oracle`, 2026-09-26.

No remaining findings. Reviewed the generic initialization extraction,
Environment compatibility, typed Certificate, final Example consumer, library
imports, colocated mutation runner/contracts and additive gate/documentation
wiring. One extra EOF blank line in Init was fixed; the final staged
`git diff --check` exits 0.

## Proof and statement adequacy

`Refine.Init` preserves the original logical loader proof: definition keys
distinguish the three tables, variable declarations are ignored, loads remain
ordered, and unique names imply successful checked initialization. The
unchecked table constructor is connected to `Ctx.init` by an actual theorem,
not a fabricated successful result. Existing Environment public APIs and
concrete Nano witness remain intact.

Certificate fields are typed propositions about the actual helper quotation,
generated executable, independent source representation, concrete initialized
environment and reference invocation. Membership is kernel-checked; identity
with the pinned exported source remains the independent quotation check.
Forward correspondence covers all terminating outcomes and excludes failure
on related inputs. Reverse correspondence supplies actual finite executions,
not a termination or environment premise. Its transitive proof includes the
existing generated refinement theorem and handwritten realization/representation
proofs, with exact core-three axiom guards.

The final reference commutation theorem consumes the certificate's composition
and commutation fields without changing its `SourceFields` domain. The first
actual raw output still feeds the second reference call. Finite lists, exact
byte names, duplicates, absence and scalar W/S/B/MATCH_KIND remain supported;
no typing/range, nested-value, extern, printing or arbitrary assignment
reordering claim was added. The bundle is not a names-only dependency report
or automatic reverse-certificate generator.

## Mutation and integration boundaries

The frozen runner compiles temporary artifact copies without modifying tracked
generated sources. An unchanged baseline passes before mutants are accepted.
The behavior mutant is checked against the emitted AL-refinement proof under
the original Nano namespace/environment, with kernel-equal source quotation;
its runtime comparison separately supplies a concrete disagreement. The
quotation mutant fails comparison with the decoded export, and the unsigned
to signed representation mutant fails the representation proof and observation.

Exit codes, fresh nonce reports, intended diagnostic prefixes and proof-line
boundaries are checked. Timeouts, warning/sorry diagnostics, stale/missing
reports, unrelated compiler failures and absent mutations fail the harness.
Selected artifact sensitivity is explicitly distinguished from mutating the
generator implementation or comprehensive fault coverage.

The gate additions require the new files, run runner contracts unconditionally,
and run the real mutation checks after quotation checking in the Lean section,
propagating failures. Existing gates are unweakened; no network/upstream capture,
new general CLI or generic framework was introduced. Navigation, design,
decision, roadmap and tactic-pitfall descriptions match the bounded behavior.

## Independent checks

All commands used the pinned Nix shell:

- Direct Lean checks of Init, Certificate and Example: actual exit 0, including
  their exact axiom audits.
- Colocated `test/test_runner.py`: eight tests, exit 0.
- Colocated `test/run.py`: actual exit 0; baseline checked, behavior rejected
  at `update_fieldValue.refines_group`, quotation rejected at `compareSpecs`,
  representation rejected at `Scalar.sourceRel`.
- `bash -n scripts/check.sh` and final staged diff whitespace check: exit 0.

Root's full gate session 7692 was still running at this checkpoint; this review
does not claim its verdict or remote CI. No full Lake build/gate was run by the
reviewer. Only this report was written; no source edits, staging or commits.
