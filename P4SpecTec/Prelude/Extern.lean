import Lean.Data.Json.Printer
import P4SpecTec.Prelude.Value

/-!
Extern values: the opaque state a target keeps inside the spec's values.
Mirrors `ExternV of Yojson.Safe.t`: the state is JSON the target
interprets, so an `extern syntax` in a spec becomes this type (design
section 5.4).
-/

namespace P4SpecTec.Prelude

/-- The value of an `extern syntax` type: JSON owned by the target. -/
structure ExternValue where
  /-- The target's state. -/
  json : Lean.Json

instance : BEq ExternValue := ⟨fun a b => a.json.compress == b.json.compress⟩

instance : ToValue ExternValue :=
  ⟨fun e => Runtime.Value.Make.mk (Value.varT "extern") (.ExternV e.json)⟩

instance : OfValue ExternValue :=
  ⟨fun _ v => match v.it with | .ExternV j => some ⟨j⟩ | _ => none⟩

/-- The empty state, `null`. -/
def ExternValue.null : ExternValue := ⟨.null⟩

end P4SpecTec.Prelude
