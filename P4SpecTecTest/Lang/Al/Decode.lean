import P4SpecTec.Lang.Al.Json

/-!
The committed Nano-P4 export decodes completely, and the count of
definitions by kind is the one upstream's `algo` printed when the export
was made (`.agents/status.md` records the numbers).
-/

open P4SpecTec.Lang.Al in
/-- Decode the export and count definitions by constructor. -/
def countDefs : IO (List (String × Nat)) := do
  let spec ← Json.readSpec "exports/nano-p4.al.json"
  let kinds := spec.map fun d => match d.it with
    | .ExternTypD .. => "ExternTypD" | .TypD .. => "TypD" | .VarD .. => "VarD"
    | .ExternRelD .. => "ExternRelD" | .RelD .. => "RelD" | .ExternDecD .. => "ExternDecD"
    | .BuiltinDecD .. => "BuiltinDecD" | .TableDecD .. => "TableDecD" | .FuncDecD .. => "FuncDecD"
  let names := ["VarD", "BuiltinDecD", "FuncDecD", "TypD", "ExternTypD", "RelD", "ExternRelD"]
  pure (names.map fun n => (n, kinds.count n))

/-- The counts in the order VarD, BuiltinDecD, FuncDecD, TypD, ExternTypD,
RelD, ExternRelD. -/
def counts : IO (List Nat) := do pure ((← countDefs).map (·.2))

/-- info: [8, 26, 76, 161, 1, 77, 1] -/
#guard_msgs in #eval counts

-- Invalid transport bytes must not be silently replaced before JSON parsing.
#guard match P4SpecTec.Util.Yojson.parseBytes (ByteArray.mk #[34, 255, 34]) with
  | .error "JSON input is not valid UTF-8" => true
  | _ => false

#guard match P4SpecTec.Util.Yojson.parseBytes "\"é\"".toUTF8 with
  | .ok (.str text) => text.toUTF8 == ByteArray.mk #[0xc3, 0xa9]
  | _ => false

#guard match P4SpecTec.Lang.Il.Json.exp' (.arr #[.str "TextE", .str "é"]) with
  | .ok (.TextE text) => text.toBytes == ByteArray.mk #[0xc3, 0xa9]
  | _ => false

#guard !(P4SpecTec.Util.Yojson.parseBytes "\"\\uD800\"".toUTF8).isOk
#guard !(P4SpecTec.Util.Yojson.parseBytes "\"\\uDC00\"".toUTF8).isOk
#guard !(P4SpecTec.Util.Yojson.parseBytes "\"\\uD800x\"".toUTF8).isOk
#guard !(P4SpecTec.Util.Yojson.parseBytes "\"\\uD800\\u0041\"".toUTF8).isOk
#guard match P4SpecTec.Util.Yojson.parseBytes "\"\\uD83D\\uDE00\"".toUTF8 with
  | .ok (.str text) => text == "😀"
  | _ => false
#guard match P4SpecTec.Util.Yojson.parseBytes "\"\\\\uD800\"".toUTF8 with
  | .ok (.str text) => text == "\\uD800"
  | _ => false
