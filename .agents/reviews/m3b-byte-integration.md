# M3B semantic byte-text integration review

2026-09-25. Independent agent review of `m3b-byte-semantics` against
`5aeae5b`, including the fixes made during review. Code review was read-only;
this report is the only file the reviewer changed. No commit or push.

## Verdict

No outstanding high/medium findings in the frozen integration slice.
Two semantic findings were identified, fixed and independently rechecked.
This is not approval of full-P4 completion or stateful integration. The
full integration gate remains the author's next checkpoint.

## Findings resolved

### High: text exceptions were incorrectly retryable

The initial optional text wrappers used `Eval.unmatch?`; the value-level
dispatcher likewise turned every absent result into a mismatch. Upstream
`interface/builtin/texts.ml` can instead raise hard `Failure`,
`Invalid_argument`, assertion or runtime-value exceptions. Its
`interp/interp-al/interp.ml:1504` catches only
`Builtin.Error.BuiltinError`, and `interface/builtin/call.ml:103` does not
translate other exception classes. Retrying a fallback after those failures
changes the algorithm's result. The initial oracle's catch-all `error`
category masked this difference.

Fixed in `Codegen/Funcs.lean:builtinBody` and
`Interface/Builtin/Call.lean:invokeText`/`invokeWithHints`:

- The four optional text operations now use `Eval.err?` in generated code.
- Checked dispatch validates zero type arguments and value arity first,
  preserving retryable extraction errors. A correctly applied operation's
  conversion/operation failure becomes a hard error.
- The legacy Option dispatcher remains explicitly kind-erasing; the
  interpreter and new oracle use checked dispatch.
- `test/text/probe.ml` records actual exception classes. The consumer
  rejects unknown classes and distinguishes hard errors from BuiltinError.

Independent reruns observed 31 successes, 11 `Failure` exceptions and four
`Assert_failure` exceptions at the pinned upstream revision. All 46 agree
with checked dispatch, interpreter calls and production-emitted wrappers;
the four applicable real Nano wrappers also agree. A sensitivity probe
changing an invalid-number case to `builtin_error`, generic `error`, or
`other` is rejected. A failing numeric call under sequential choice remains
`Fail.err`, not a successful fallback. Wrong arity/typearity remains a
mismatch, while a wrong value kind at correct arity is a hard error.

### Medium: malformed Unicode escapes were silently replaced

The original `Util/Yojson.lean:parseBytes` validated raw UTF-8 but then
delegated to Lean's JSON parser, which replaces lone/malformed surrogate
escapes with U+FFFD. Direct reproduction accepted `"\\uD800"`,
`"\\uDC00"`, and `"\\uD800x"` with changed content.

Fixed by `validateEscapes`, which scans byte-level quote/escape structure
before parsing. Independent tests reject lone/repeated high surrogates,
lone low surrogates including object keys, invalid pairs, overlong UTF-8,
and UTF-8-encoded surrogate code points. Valid pairs, including the maximum
pair, escaped quotes and literal escaped backslashes remain accepted.

The boundary is deliberately narrower than arbitrary OCaml strings:
pinned Yojson rejects lone high surrogates but can decode lone low
surrogates into invalid UTF-8 bytes. Lean ingress rejects both rather than
silently changing them. This restriction is documented, not claimed as
general lossless transport.

## Other invariants checked

- `Lang/Il/Ast.lean` changes semantic `text`, TextE and TextV to ByteText;
  identifiers, atoms and generic JSON strings remain String.
- `Runtime/Value/Value.lean` compares unsigned byte sequences.
  `Refine/Value.lean` and `Refine/Calc.lean` retain canonical-value equality
  and text inversion through the proved byte comparison/equality law.
  Direct elaboration of both proof modules and their audits succeeds.
- `Prelude/Iter.lean` and the interpreter count/index/slice bytes.
  Bounds and replacement lengths are checked without rejecting a valid
  operation merely because its result is invalid UTF-8.
- `Codegen/Exp.lean` retains base, replacement, then index evaluation
  order for root updates. Unsupported sliced/nested update paths remain
  explicit rejections rather than approximations.
- `Codegen/Fmt.lean:textLit` emits valid UTF-8 through explicit encoding
  and invalid UTF-8 through explicit bytes. Updates tests actually parse,
  elaborate and run emitted Unicode/raw literals, raw quotation, byte
  length/index/slice/concatenation and byte replacement.
- Text splitting, prefix/suffix stripping and space removal operate on
  bytes. Numeric parsing matches the recorded empty/sign/prefix/underscore,
  invalid-byte and large-integer observations. The oracle is evidence for
  these cases, not a completeness proof for every Bigint parser input.
- Existing corrupt expected-output files now fail both differential
  runners instead of disabling output comparison. The boundary test uses
  a passing control program and mutates only ignored source-location text,
  so schema rejection cannot conceal a lossy transport decoder.
- Reviewed the updated primary-worktree `docs/design.md`,
  `.agents/decisions.md`, and `.agents/notes/byte-text.md`. Their claims
  distinguish internal arbitrary bytes, restricted JSON ingress, observed
  builtin behavior and remaining full-P4 work.

## Independent validation

Commands ran from `/Users/qobilidop/my/work/p4-spectec-lean-byte-text` under
`nix develop /Users/qobilidop/my/work/p4-spectec-lean --command`, except the
upstream oracle, which used that flake's `#upstream` shell. All listed
checks exited 0:

- Direct `lake env lean` elaboration of `P4SpecTecTest/Builtins.lean`,
  `Decode.lean`, `Updates.lean`, `P4SpecTec/Refine/Value.lean`, and
  `P4SpecTec/Refine/Calc.lean`.
- Additional stdin Lean sensitivity guards for malformed/valid Unicode,
  checked-dispatch failure kinds, hard-error fallback suppression, and
  oracle rejection of misclassified/unknown failures.
- `python3 test/text/run.py --check --upstream
  /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec`: all 46
  classified observations reproduced at
  `8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3`.
- Existing compiled `check-text-builtins --upstream` with the same absolute
  upstream path: 46 dispatcher/interpreter/emitted-wrapper checks and
  four Nano-wrapper checks passed.
- Improved `test/diff/test_json_boundary.py`: both passing controls,
  raw invalid UTF-8 and high/low surrogate input rejection, and malformed
  existing expectations passed on both actual differential binaries.
- `git diff --check 5aeae5b` and focused Lean line-length/whitespace checks.

No full gate, full-P4 regeneration/build, complete corpus rerun, or rerun
of all 18 generated refinement proofs was performed by this reviewer.
Those broader author checks must be recorded separately. This review
does not establish stateful integration, byte-preserving arbitrary source
literal transport, full text-builtin refinement/completeness, or correct
failure classification for all remaining legacy builtin families.
