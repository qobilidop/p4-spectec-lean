import P4SpecTec.BackendSim.Placeholder

/-!
The placeholder target's extern dispatch and `static_assert`, against a recording
callback: lookup order, the returned value, and which failures are errors or mismatches.
Agreement with upstream is the corpus replay's obligation, and it covers the successful
branch only: a failed `static_assert` is an upstream abort, which the replay does not
evaluate, so that branch follows a reading of `placeholder.ml` and `core/func.ml`.
-/

namespace P4SpecTecTest.PlaceholderTarget

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Runtime P4SpecTec.Lang.Il
open P4SpecTec.Util.Source P4SpecTec.BackendSim

/-- Failure over a log of the names looked up, retained across failure. -/
private abbrev M := ExceptT Fail (StateM (List ByteText))

private def p4Bool (b : Bool) : value :=
  Value.Make.case (.VarT (mkPhrase "value") [])
    (.Seq [.Atom (mkPhrase (.Tag "B")), .Arg (Value.Make.bool b)])
private def text (s : String) : value := Value.Make.text (ByteText.ofString s)
private def names (ss : List String) : value := Value.Make.list .TextT (ss.map text)
private def ctx : value := text "typing context"

/-- A typing context where `check` is the given value; `message` may be absent. -/
private def lookups (check : value) (message : Bool) : Placeholder.Call M :=
  fun name _ values => do
    let [prefixed, cursor, context] := values | throw .err
    let .CaseV (.Seq [.Atom tag, .Arg bare]) := prefixed.it | throw .err
    let .CaseV (.Atom local_) := cursor.it | throw .err
    unless name == "find_var_value_t" && tag.it == .Tag "BARE" &&
        local_.it == .Keyword "LOCAL" && Value.eq context ctx do throw .err
    let some key := Value.Get.text bare | throw .err
    modify (· ++ [key])
    if key == ByteText.ofString "check" then pure check
    else if key == ByteText.ofString "message" && message then pure (text "why")
    else throw .unmatch

private def run (call : Placeholder.Call M) (relation function : String)
    (parameters : List String) : Except Fail (List value) × List ByteText :=
  ((Placeholder.externInterface (m := M)).eval_extern_rel call relation
    [ctx, text function, names parameters]).run.run []

private def lctk := "ExternFunctionCall_eval_lctk"

private def returns (r : Except Fail (List value) × List ByteText) (v : value)
    (log : List String) : Bool :=
  match r with
  | (.ok [x], seen) => Value.eq x v && seen == log.map ByteText.ofString
  | _ => false

private def fails (r : Except Fail (List value) × List ByteText) (kind : Fail)
    (log : List String) : Bool :=
  match r with
  | (.error actual, seen) => actual == kind && seen == log.map ByteText.ofString
  | _ => false

-- A true check is returned as it is; the message is looked up first when declared.
#guard returns (run (lookups (p4Bool true) true) lctk "static_assert" ["check"])
  (p4Bool true) ["check"]
#guard returns (run (lookups (p4Bool true) true) lctk "static_assert" ["check", "message"])
  (p4Bool true) ["check", "message"]
-- A false or malformed check is a hard error, after the same lookups.
#guard fails (run (lookups (p4Bool false) true) lctk "static_assert" ["check", "message"])
  .err ["check", "message"]
#guard fails (run (lookups (text "not a boolean") true) lctk "static_assert" ["check"])
  .err ["check"]
-- A failed callback is a mismatch, whichever kind the callee produced (`call_func`).
#guard fails (run (lookups (p4Bool true) false) lctk "static_assert" ["check", "message"])
  .unmatch ["check", "message"]
#guard fails (run (fun _ _ _ => throw .err) lctk "static_assert" ["check"]) .unmatch []
-- Other functions, parameter lists and relations are errors without any lookup.
#guard fails (run (lookups (p4Bool true) true) lctk "other" ["check"]) .err []
#guard fails (run (lookups (p4Bool true) true) lctk "static_assert" ["message"]) .err []
#guard fails (run (lookups (p4Bool true) true) lctk "static_assert" []) .err []
#guard fails (run (lookups (p4Bool true) true) "ExternFunctionCall_eval" "static_assert"
  ["check"]) .err []
#guard fails (run (lookups (p4Bool true) true) "ExternMethodCall_eval" "static_assert"
  ["check"]) .err []
#guard match ((Placeholder.externInterface (m := M)).eval_extern_rel
    (lookups (p4Bool true) true) lctk [ctx, text "static_assert"]).run.run [] with
  | (.error .err, []) => true
  | _ => false

-- The two initializers return null extern values with their type notes; others fail.
private def initialized (function : String) : Except Fail value :=
  (((Placeholder.externInterface (m := M)).eval_extern_func function [] [ctx]).run.run []).1
private def nullExtern (r : Except Fail value) (type : String) : Bool :=
  match r with
  | .ok v => Value.eq v (Value.Make.extern (.VarT (mkPhrase type) []) .null) &&
      (match v.it, v.note.typ with
        | .ExternV .null, .VarT name [] => name.it == type
        | _, _ => false)
  | .error _ => false
#guard nullExtern (initialized "init_objectState") "objectState"
#guard nullExtern (initialized "init_archState") "archState"
#guard match initialized "init_other" with
  | .error .err => true
  | _ => false

end P4SpecTecTest.PlaceholderTarget
