import ExampleProofs.NanoP4FieldUpdate.Domain
import ExampleProofs.NanoP4FieldUpdate.Representation
import ExampleProofs.NanoP4FieldUpdate.Semantics
import ExampleProofs.NanoP4FieldUpdate.Environment
import ExampleProofs.NanoP4FieldUpdate.Correspondence
import ExampleProofs.NanoP4FieldUpdate.Certificate
import ExampleProofs.NanoP4FieldUpdate.Laws
import ExampleProofs.NanoP4FieldUpdate.Example

/-!
# Downstream verification examples

Examples of using the reusable libraries and generated models for downstream
verification. The Nano-P4 field-update example connects a bounded scalar slice
to the Lean AL reference; it is not certification of all Nano-P4 or full P4.
Build explicitly with `lake build ExampleProofs`; the full gate includes it.
-/
