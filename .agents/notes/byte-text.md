# Semantic byte text

2026-09-25. The reviewed ByteText foundation preserves arbitrary byte
sequences through bounds-checked index/slice/update operations, with
explicit UTF-8 encode/checked decode and proved equality/compare-equality laws.
It does not yet change the existing String-based semantic substrate.

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
- `Interface/P4/Unparse.lean`: escape raw semantic bytes. It already
  iterates UTF-8 bytes of String; identifier/atom rendering remains String.
  Printer output can be encoded explicitly when used as a text value.
- `Refine/Value.lean`, `Refine/Calc.lean`, `Tactic/Refine.lean`:
  canonical text payloads, comparison/equality and literal inversion.
  Preserve the existing kernel proofs rather than excluding text cases.
- Update fixtures and generated quotations, then run both differential
  legs and every existing refinement/axiom audit.

## Boundaries to establish

JSON's Unicode strings are not an arbitrary-byte transport. The pinned
exports can be decoded without changing their stored format, but this
alone does not prove a lossless general transport for invalid-byte source
literals. Audit parsing/export separately; fail closed rather than using
lossy UTF-8 conversion. Runtime byte texts must remain arbitrary bytes.

Add pinned upstream observations for non-ASCII and invalid-byte operations
using byte arrays/hex in the fixture boundary. Cover byte bounds, exact
replacement lengths, concatenation/order, and text builtin behavior.
The pre-existing Bigint.of_string compatibility gap must not disappear
from the work list during representation migration.

Only after full integration may the two full-P4 text updates be enabled.
Do not describe a passing foundation test as full-P4 generation, a Unicode
input transport proof, or full text-builtin compatibility.
