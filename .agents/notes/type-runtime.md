# Checked type-runtime tranche

Isolated branch `m3c-type-runtime`, based on `origin/main` `b08ab8e`.
This is a bounded M3C interpreter-fidelity increment, not corpus coverage.

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
checks passed. No gate integration, full corpus replay, full local gate or
push is claimed. Root independently reviewed the implementation and reran
TypeRuntime, the pinned fourteen cases and three offline tests (all exit 0),
with no remaining bounded findings: `.agents/reviews/m3c-type-runtime.md`.
CI wiring and integrated full/remote gates remain separate obligations.
