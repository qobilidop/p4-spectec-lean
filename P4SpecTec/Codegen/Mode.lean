import P4SpecTec.Codegen.Fmt
import P4SpecTec.Lang.Al.Ast

/-! Execution carriers selected from declarations, not library names. -/

namespace P4SpecTec.Codegen

/-- A specification has one uniform callable ABI. -/
inductive ExecMode where
  /-- No fresh-state declaration. -/
  | pure
  /-- Every callable and callback threads explicit fresh state. -/
  | freshState
  deriving BEq, Inhabited, Repr

/-- Select effects only from the actual builtin declaration. -/
def ExecMode.ofSpec (spec : Lang.Al.spec) : ExecMode :=
  if spec.any (fun d => match d.it with
      | .BuiltinDecD i .. => i.it == "fresh_typeId"
      | _ => false) then .freshState else .pure

/-- The external result ABI, with state supplied only at session boundaries. -/
def ExecMode.result (mode : ExecMode) (t : Term) : Term :=
  match mode with
  | .pure => .call "Option" [.call "Except" [.atom "Fail", t]]
  | .freshState => .binop "→" (.atom "FreshState")
      (.call "Option" [.binop "×" (.call "Except" [.atom "Fail", t]) (.atom "FreshState")])

/-- Lift a pure evaluation helper without introducing a session boundary. -/
def ExecMode.lift (mode : ExecMode) (t : Term) : Term :=
  match mode with
  | .pure => t
  | .freshState => .call "StateEval.liftEval" [t]

end P4SpecTec.Codegen
