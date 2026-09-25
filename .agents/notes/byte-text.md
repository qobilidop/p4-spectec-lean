# Semantic byte text

2026-09-25. The reviewed ByteText foundation preserves arbitrary byte
sequences through bounds-checked index/slice/update operations, with
explicit UTF-8 encode/checked decode and proved equality/compare-equality laws.
The integration checkpoint wires this representation through the semantic
substrate; identifiers and atoms deliberately remain String.

## Why the change is necessary

OCaml text is bytes. Lean String carries a UTF-8 validity proof. Replacing
byte zero of `é` (`c3 a9`) with `X` produces `58 a9`, which is not valid
UTF-8. A character replacement changes the operation, while rejecting the
result changes upstream's success into failure. ByteArray-backed text
represents the exact result without loss or an opaque escape hatch.

## Integration inventory

The read-only inventory was performed by GPT-6 Luna and checked against
the current sources. Keep names/identifiers/atoms as their existing String
representations; never change the generic JSON string decoder globally.

- `Lang/Il/Ast.lean`: semantic `text` alias and TextV payload, separate
  from `id'` and Atom strings.
- `Lang/Il/Json.lean`: TextV/TextE decoding only; generic `Yojson.str`
  also decodes identifiers and must remain separate.
- `Runtime/Value/Value.lean`: Make/Get.text and text comparison.
- `Prelude/Value.lean`: semantic ToValue/OfValue instances;
  `Prelude/Iter.lean`: byte-oriented index/slice helpers.
- `Codegen/Types.lean`: TextT representation; `Exp.lean`: literals,
  length/index/slice/update; `Reify.lean`: semantic literal quotation,
  not identifier quotation. Regenerate output; never hand-edit it.
- `Interface/Builtin/Texts.lean` and Call: integer conversion, splitting,
  prefix/suffix/space stripping and result adapters.
- `Interp/InterpAl/Interp.lean`: text literals, concatenation, length,
  indexing, slicing and both update forms.
- `Interface/P4/Unparse.lean`: escape raw semantic ByteText bytes;
  identifier/atom rendering remains String.
  Printer output can be encoded explicitly when used as a text value.
- `Refine/Value.lean`, `Refine/Calc.lean`, `Tactic/Refine.lean`:
  canonical text payloads, comparison/equality and literal inversion.
  Preserve the existing kernel proofs rather than excluding text cases.
- Update fixtures and generated quotations, then run both differential
  legs and every existing refinement/axiom audit.

## Boundaries and regression evidence

JSON's Unicode strings are not an arbitrary-byte transport. The pinned
exports can be decoded without changing their stored format, but this
alone does not prove a lossless general transport for invalid-byte source
literals. Ingress now checks raw UTF-8 and rejects unpaired JSON surrogate
escapes before Lean's parser can replace them. Pinned Yojson itself rejects
lone high surrogates but can decode lone low surrogates to invalid UTF-8;
we reject both. A general arbitrary-byte export format remains separate
work. Runtime byte texts remain arbitrary bytes.

Pinned upstream text-builtin observations use hex payloads and distinguish
BuiltinError from hard exception classes. The consumer exercises checked
dispatch, interpreter calls and production-emitted wrappers. Integer parsing
now includes the observed signed/prefixed/underscore/empty-string behavior;
the observations do not prove all Bigint.of_string inputs equivalent.
Focused guards cover byte bounds, exact replacement length, invalid UTF-8
results, compiled literals/quotations, length/index/slice/concatenation and
surrogate rejection. The differential harness separately verifies that an
existing corrupt expectations file fails rather than disabling comparison.

The two full-P4 text updates are enabled. This is not yet a full-P4 build,
a Unicode input transport proof, full text-builtin completeness or an audit
of failure classification in the remaining builtin families. Exact checks
and remaining obligations are recorded in status.
