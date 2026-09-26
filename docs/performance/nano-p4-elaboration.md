# Elaboration times: NanoP4Spec

Historical per-module durations reported by Lake when rebuilding the selected
library with `scripts/time-elab.sh NanoP4Spec`. Dependencies may remain cached.
See [Performance](../performance.md) for interpretation and reproduction.
This snapshot is not checked by CI.

- Toolchain: leanprover/lean4:v4.34.1
- Machine: arm64, Darwin 25.6.0
- Date: 2026-09-25

| Module | Seconds |
|---|---|
| NanoP4Spec.Refinement.split_dataplane_parameters | 89.00 |
| NanoP4Spec.Refinement.directionless_trailing_p | 79.00 |
| NanoP4Spec.Refinement.update_fieldValue | 66.00 |
| NanoP4Spec.Refinement.exit_e | 62.00 |
| NanoP4Spec.Refinement.find_action_p | 57.00 |
| NanoP4Spec.Refinement.params_of_callableTypeDef | 51.00 |
| NanoP4Spec.Refinement.exit_t | 42.00 |
| NanoP4Spec.Refinement.forall_ | 38.00 |
| NanoP4Spec.Refinement.flatten_parserLocalDeclarationList | 38.00 |
| NanoP4Spec.Refinement.flatten_externMethodPrototypeList | 38.00 |
| NanoP4Spec.Refinement.flatten_typeFieldList | 37.00 |
| NanoP4Spec.Refinement.flatten_tableEntryList | 37.00 |
| NanoP4Spec.Refinement.flatten_selectCaseList | 37.00 |
| NanoP4Spec.Refinement.flatten_program | 37.00 |
| NanoP4Spec.Refinement.flatten_statementList | 36.00 |
| NanoP4Spec.Refinement.flatten_controlLocalDeclarationList | 36.00 |
| NanoP4Spec.Refinement.exists_ | 28.00 |
| NanoP4Spec.Refinement.find_action | 19.00 |
| NanoP4Spec.«5.13-typing-call-convention» | 4.20 |
| NanoP4Spec.«1-syntax» | 3.90 |
| NanoP4Spec.«8.14-eval-convention» | 3.00 |
| NanoP4Spec.«5.01-typing-relation» | 3.00 |
| NanoP4Spec.«3.1-operations» | 1.90 |
| NanoP4Spec.«2.1-ir» | 1.70 |
| NanoP4Spec.«8.01-eval-relation» | 1.60 |
| NanoP4Spec.«5.02-typing-type» | 1.50 |
| NanoP4Spec.«7.1-load-declaration» | 1.10 |
| NanoP4Spec.«8.09-eval-parser» | 1.00 |
| NanoP4Spec.«5.08-typing-declaration» | 1.00 |
| NanoP4Spec.«5.00-typing-context» | 0.85 |
| NanoP4Spec.«8.00-eval-context» | 0.77 |
| NanoP4Spec.«3.0-value» | 0.75 |
| NanoP4Spec.«8.04-eval-lvalue» | 0.67 |
| NanoP4Spec.«9-nano-switch» | 0.62 |
| NanoP4Spec.«5.06-typing-parameter» | 0.59 |
| NanoP4Spec.«0-stdlib» | 0.55 |
| NanoP4Spec.«7.0-load-context» | 0.54 |
| NanoP4Spec.«3.2-bits» | 0.49 |
| NanoP4Spec.«8.10-eval-control» | 0.47 |
| NanoP4Spec.«5.09-typing-parser» | 0.43 |
| NanoP4Spec.«5.11-typing-table» | 0.41 |
| NanoP4Spec.«8.11-eval-table» | 0.39 |
| NanoP4Spec.Refinement.Spec | 0.38 |
| NanoP4Spec.Refinement | 0.38 |
| NanoP4Spec.«5.07-typing-argument» | 0.37 |
| NanoP4Spec.«5.04-typing-lvalue» | 0.37 |
| NanoP4Spec | 0.35 |
| NanoP4Spec.«2.0-domain» | 0.32 |

Sum of module durations: 860.6s over 48 modules (not elapsed build time).
