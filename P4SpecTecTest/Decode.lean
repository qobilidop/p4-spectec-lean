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
