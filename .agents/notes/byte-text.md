# Semantic byte text

Compacted 2026-09-26; decision and observations dated 2026-09-25 at upstream
`8c8e0c6f`. Original note and `m3b-byte-text.md`/`m3b-byte-integration.md`
reviews are recoverable under their former paths at Git `968ad65`.
Durable boundary evidence with paused follow-ups, not a new semantic review.

## Representation and transport

Use ByteArray-backed `ByteText` for semantic text; identifiers, atoms and
generic JSON strings remain Lean String. OCaml text is arbitrary bytes:
replacing byte zero of `é` (`c3 a9`) with `X` yields `58 a9`, an upstream
result Lean String cannot represent. Character operations or UTF-8 rejection
change semantics. ByteArray permits direct storage/access; decoding is checked.
Proved equality/compare-equality laws do not assert order transitivity.

Integration covers TextE/TextV and dedicated JSON decoders, runtime Make/Get/
comparison, ToValue/OfValue, byte index/slice/update, generated TextT/literals/
quotations, six text builtins and checked dispatch, interpreter operations,
Unparse byte escaping and refinement inversion. UTF-8 generated literals use
explicit encoding; invalid literals use bytes. Generic `Yojson.str` also
handles names and must stay separate. GPT-6 Luna independently prepared the
integration inventory.

Bounds and exact replacement length are checked; text replacement requires
one byte. Preserve base/replacement/index order. Nested and sliced update
paths remain rejected. Both full-P4 text update sites can emit, which is not
a full-P4 build. List-update evidence: [generated encodings](generated-encodings.md).

JSON ingress rejects invalid raw UTF-8 and unpaired surrogate escapes before
Lean's parser substitutes U+FFFD. Pinned Yojson rejects lone high surrogates
but may decode lone low surrogates into invalid UTF-8; Lean deliberately
rejects both. Internal text still represents arbitrary bytes. General
byte-preserving source-literal export remains open. Confidence high for
internal semantics/restricted ingress; revisit for arbitrary-byte source
literals or measured proof/storage cost.

## Failure classification and recorded review

Checked dispatch validates arity/type arity first (retryable extraction
mismatch); a correctly applied operation's conversion/operation failure is
hard `Fail.err`. Upstream catches `BuiltinError`, not `Failure`,
`Assert_failure` or `Invalid_argument`. An early Option wrapper and catch-all
oracle wrongly made those exceptions retryable; review corrected generated
wrappers to `Eval.err?`, checked dispatch and classified observations.
Legacy Option dispatch remains kind-erasing. The six text builtins and
printer audit does not establish classification for other builtin families.

GPT-6 Sol independently reviewed another Sol agent's foundation from
`3b8175f`: no findings, ByteText focused build exit 0 (three jobs), audits
and diff checks passed. A first integration gate failed on a missing
“not a mirror” header; a fresh gate passed exit 0/no skips. The reviewer did
not run that gate. Missing ignored Nano JSON also caused an early test
failure before verified unpacking and rerun.

An independent agent reviewed integration against `5aeae5b`, rechecking
resolved hard-error and surrogate-replacement findings. Direct elaborations
of Builtins/Decode/Updates and Refine Value/Calc, Unicode/failure sensitivity
probes and diff/hygiene checks exited 0. Upstream `test/text/run.py --check`
reproduced 46 cases: 31 successes, 11 Failure, four Assert_failure. Runtime
checks covered dispatch, interpreter and actual emitted wrappers, plus four
Nano wrappers. Misclassifying a failure as builtin_error/generic error/unknown
was rejected; wrong arity retried, hard numeric errors did not.

Transport sensitivity passed both actual differential binaries with controls,
invalid UTF-8, high/low surrogate escapes and corrupt existing expectations.
Corrupt expectations must fail, never disable comparison. Valid pairs,
escaped quotes/backslashes and maximum pairs remain accepted. Hex-payload
observations cover signed/prefixed/underscore/empty integer forms, invalid
bytes and large integers, not all `Bigint.of_string` inputs.

The integration reviewer did not rerun the full gate, all 18 refinements,
full-P4 generation or corpus. Separate byte/state reconciliation is in
[state review](state-integration/review.md). Open work: arbitrary-byte
transport, full text-builtin correspondence and other builtin failure kinds.
