# Status

Current checkpoint, updated 2026-09-27.

## Authorized scope

The user authorized completion of N2 after N0/N1. N2 implementation and its
strict compiled check pass. All 44 full local gate stages passed; publication and
exact-revision remote CI remain active.
N3–N6 are planned, not started. Full-P4 M3 remains paused. The compacted
[Nano plan](notes/nano-certification.md) owns scope, evidence and next milestones;
[Certification](../docs/certification.md) states current artifact guarantees.

## N2 implementation

- All 162 source type families have complete generated codecs, including recursive
  syntax, nested containers and explicit legal polymorphic dictionaries.
- Both correspondence directions cover 39/153 bodied definitions. Strict N2
  requires the original 18 plus Type_eq/ParameterType_eq, Type_ok and Var_init
  with their complete 30-definition dependency/SCC closure.
- All 26 builtins have dispatch, both invocation directions and independent
  source input/output contracts. Source entry, output preservation and full
  intermediate call admission are separately checked; no caller precondition
  is inferred from decoder success or output preservation alone.
- Schema 3 covers representations and source profiles: primitive/contextual
  codecs, eight typed schematic-variable omissions and actual table initialization.
  The source domain is the pinned constructor grammar, distinct from permissive
  runtime subtype membership. Numeric casts and optional wrappers justify this
  boundary; actual producer/call proofs establish composition.
- The full gate now requires `--require-n2`. Its successful result leaves broader
  core, target and release obligations independent: 888 obligations, 381 bindings,
  507 unresolved. Full Nano certification is not claimed.

## Checked evidence

Production `lake build --wfail NanoP4Spec.Refinement` passed session 16874,
621 jobs; Type_eq took 235s and Var_init producer 589ms. Generation writes 511
current files. No generated source was patched by hand. Source-table/variable
quotation checks pass, with 342 ordinary declarations and 8 typed variables.
Independent reviews found no unresolved semantic issue; exact file hashes,
reviewer provenance and original limits are retained in
[nano-certification-review.json](notes/nano-certification-review.json).

The first full-gate attempt 46818 returned exit 1 on legacy fixture/formatting
issues. The second 54175 passed library, all Lean tests, strict compiled N2,
quotation, generation and replay stages; only the downstream example's two
unused simp facts failed `--wfail`. These facts were removed without changing
the theorem or its axiom audit; explicit `lake build --wfail ExampleProofs`
then passed 60286. The final full gate passed with recorded exit 0 (session 40389),
all 44 stages and no skips. Tested index tree:
`e654712bd9385535ec73c3a88b883b57054036fe`.
Evidence: `.artifacts/n2-closure-gate.{log,json}`. Later changes are checkpoint
prose only; executable inputs are unchanged.

Other resolved integration findings: Unit/pair fixtures now reflect supported
shapes and retain malformed-mode/unsupported-arity negatives; a reserved test
binder is renamed; mutation extraction binds the exact generated outcome clause.
The actual field-update mutation runner passed in 18s in the full gate. The obsolete
631-line handwritten TypeIR encoding probe was retired after five production
codec/totality replacement witnesses passed with audits (80617); no unique negative
or mutation test was removed.

## Publication and next action

Work is on `n2-certification`; last local commit is `709326f`, preceded by `feec9b6`,
`996dc22` and `9863160`. The implementation is staged but not yet committed or pushed.
Published main remains `c8f78f7` with successful
[CI 36294851006](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36294851006).
Next: commit with the session coauthor trailer, fast-forward main, push and
verify its exact remote CI revision. Then remove the finished branch and mark N2 closed. N3's
first proposed work is Program_load/Expr_eval dependency closures, not automatic
work during publication.

The older docs/repository-review branch and local archive backup are preserved.
One worktree remains; upstream's expected four-file exporter patch remains applied.
No source pins changed. N1 closed at `56cf92c2201e25c11d1263cbdf6895a827afc612` with
[CI 36290916636](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36290916636).
