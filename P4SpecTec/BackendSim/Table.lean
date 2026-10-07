import P4SpecTec.BackendSim.SpecImpl.Func

/-!
Port of `p4spec/lib/backend-sim/table.ml`: the match-action table interface of the STF
driver, over the spec's table functions through the function trampoline. A qualified table
name is looked up as an object path first and by its last component otherwise; an entry
whose key names the table does not know is retried with the table's own key names in
order, as upstream does. Every `Option.get`, `List.nth` and `List.map2` upstream raises
on is the hard error `Fail.err`.
-/

namespace P4SpecTec.BackendSim.Table

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude P4SpecTec.Util.Source
open P4SpecTec.BackendSim.SpecImpl

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- Mirrors `String.split_on_char '.'` on the bytes of a name. -/
def splitDots (name : ByteText) : List ByteText := Id.run do
  let mut parts := #[]
  let mut current := ByteArray.empty
  for b in name.bytes.data do
    if b == 46 then
      parts := parts.push (ByteText.ofBytes current)
      current := ByteArray.empty
    else current := current.push b
  pure (parts.push (ByteText.ofBytes current)).toList

/-- The object identifier of a qualified table name, under the type `nameIR*`. -/
private def qualifiedId (names : List ByteText) : value :=
  Value.Make.list (.IterT (mkPhrase (.VarT (mkPhrase "nameIR") [])) .List)
    (names.map Value.Make.text)

/-- Mirrors `find_table`. -/
def find_table (call : Func.Call m) (value_arch value_tableName : value) : m value := do
  let find_table_unqualified := fun (name : ByteText) => do
    Func.required (← Func.find_object_unqualified_e call value_arch (Value.Make.text name))
  let table_name ← Func.required (Value.Get.text value_tableName)
  match splitDots table_name with
  | [] => throw .err
  | [unqualified] => find_table_unqualified unqualified
  | names =>
    match ← Func.find_object_qualified_e call value_arch (qualifiedId names) with
    | some value_table => pure value_table
    | none =>
      let some unqualified := names.getLast? | throw .err
      find_table_unqualified unqualified

/-- Mirrors `update_table`. -/
def update_table (call : Func.Call m) (value_arch value_tableName value_tableObject : value) :
    m value := do
  let update_table_unqualified := fun (name : ByteText) =>
    Func.update_object_unqualified_e call value_arch (Value.Make.text name) value_tableObject
  let table_name ← Func.required (Value.Get.text value_tableName)
  match splitDots table_name with
  | [] => throw .err
  | [unqualified] => update_table_unqualified unqualified
  | names =>
    let value_objectId := qualifiedId names
    if (← Func.find_object_qualified_e call value_arch value_objectId).isSome then
      Func.update_object_qualified_e call value_arch value_objectId value_tableObject
    else
      let some unqualified := names.getLast? | throw .err
      update_table_unqualified unqualified

/-- Mirrors the retry of `add_entry`: the keyset's names replaced by the table's own
non-selector key names, in order; a length mismatch raises upstream's `List.map2`. -/
private def renamed_keyset (call : Func.Call m) (value_tableObject value_tableKeysetInterface :
    value) : m value := do
  let keys ← Func.key_interface_of_tableObject call value_tableObject
  let values_nameIR_key ← keys.filterMapM fun (value_nameIR_key, value_nameIR_matchKind, _) => do
    let kind ← Func.required (Value.Get.text value_nameIR_matchKind)
    pure (if kind == ByteText.ofString "selector" then none else some value_nameIR_key)
  let values_tableKeyInterface ← Func.required (Value.Get.list value_tableKeysetInterface)
  let values_tableKeyValueInterface ← values_tableKeyInterface.mapM fun entry => do
    let fields ← Func.required (Value.Get.tuple entry)
    Func.required fields[1]?
  unless values_nameIR_key.length == values_tableKeyValueInterface.length do throw .err
  let typ_tableKeyInterface : typ' := .VarT (mkPhrase "tableKeyInterface") []
  let typ_list : typ' := .IterT (mkPhrase typ_tableKeyInterface) .List
  pure (Value.Make.list typ_list
    ((values_nameIR_key.zip values_tableKeyValueInterface).map fun (k, v) =>
      Value.Make.tuple typ_tableKeyInterface [k, v]))

/-- Mirrors `add_entry`. -/
def add_entry (call : Func.Call m) (value_ctx value_arch value_tableName
    value_tableEntryPriorityInterface value_tableKeysetInterface value_tableActionInterface :
    value) : m value := do
  let value_tableObject ← find_table call value_arch value_tableName
  let value_tableObject ← match ← Func.tableObject_add_entry call value_ctx value_tableObject
      value_tableEntryPriorityInterface value_tableKeysetInterface value_tableActionInterface with
    | some value_tableObject => pure value_tableObject
    | none =>
      let value_tableKeysetInterface ← renamed_keyset call value_tableObject
        value_tableKeysetInterface
      Func.required (← Func.tableObject_add_entry call value_ctx value_tableObject
        value_tableEntryPriorityInterface value_tableKeysetInterface value_tableActionInterface)
  update_table call value_arch value_tableName value_tableObject

/-- Mirrors `add_default_action`. -/
def add_default_action (call : Func.Call m)
    (value_ctx value_arch value_tableName value_tableActionInterface : value) : m value := do
  let value_tableObject ← find_table call value_arch value_tableName
  let value_tableObject ← Func.tableObject_add_default_action call value_ctx value_tableObject
    value_tableActionInterface
  update_table call value_arch value_tableName value_tableObject

end P4SpecTec.BackendSim.Table
