import P4SpecTec.Codegen.StateProps
import P4SpecTec.Codegen.Certificates.RunSound

/-! Emit exact-state relation run-soundness certificates. -/

namespace P4SpecTec.Codegen.StateProps

open Std
open P4SpecTec.Codegen
open P4SpecTec.Codegen.Term
open P4SpecTec.Codegen.Funcs

/-- The binders and statement of a relation's state run-soundness theorem: a successful
run from `«@s0»` to `«@sf»` implies the logical relation at those states. -/
private def runSoundStatement (externs : Bool) (m : Props.Member) :
    Except String (Format × Format) := do
  if !m.isRel then throw "state run-soundness requires a relation"
  let ps := paramNames m.params.length
  let ext := if externs then Format.text " [Externs]" else Format.nil
  let outArg := if m.nOuts == 0 then "()" else "o"
  let obs := if m.nOuts == 0 then Format.nil
    else Format.line ++ Format.text "(o : " ++ m.ret.fmt ++ ")"
  let states := Format.line ++ "(«@s0» «@sf» : FreshState)"
  let call := (Term.call m.defName (ps.map Term.atom ++ [.atom "«@s0»"])).fmt
  let stmt := Props.eqn call (someOk (.atom outArg) "«@sf»") ++ " →" ++ Format.line ++
    m.conclusion ++ " «@s0» «@sf»"
  pure (ext ++ Props.paramBinders m.params ++ obs ++ states, stmt)

/-- The name of a relation's state run-soundness theorem, unqualified. -/
def runSoundName (m : Props.Member) : String := m.localName ++ "_sound"

/-- The exact state-indexed successful result contract of a nonrecursive relation. -/
def runSound (externs : Bool) (m : Props.Member) : Except String Format := do
  let (binders, stmt) ← runSoundStatement externs m
  pure (Format.group (Format.nest 4 (Format.text ("theorem " ++ runSoundName m) ++
    binders ++ " :" ++ Format.line ++ stmt ++
    " :=")) ++ Format.nest 2 (Format.line ++ "by state_run_sound"))

/-- The closed type of that theorem, for the coverage report. -/
def runSoundType (externs : Bool) (m : Props.Member) : Except String Format := do
  let (binders, stmt) ← runSoundStatement externs m
  pure (Format.group (Format.text "∀" ++ Format.nest 2 binders ++ "," ++ Format.line ++ stmt))

/-- The name of a recursive group's joint theorem, unqualified, after its first relation. -/
def groupSoundName (first : Props.Member) : String := first.localName ++ "_sound_group"

/-- The joint theorem of a recursive group, by induction over its least fixed point: the
conjunction of the state run-soundness statements of its relations, each the statement
`runSound` gives a relation outside recursion. Then each relation's theorem as a
projection. `qualify` qualifies a name of the library; `consumers` are the callback
consumers the group's own monotonicity proofs may expose. -/
def groupRunSound (externs : Bool) (qualify : String → String) (consumers : List String)
    (members : List Props.Member) : Except String (List Format) := do
  if let some m := members.find? (!·.tparams.isEmpty) then
    throw s!"recursive group member {m.id} has type parameters"
  let relations := members.filter (·.isRel)
  let some first := relations.head? | throw "recursive group without a relation"
  let ext := if externs then Format.text " [Externs]" else Format.nil
  let statements ← relations.mapM fun m => do pure (Format.paren (← runSoundType false m))
  let stmt := Format.joinSep statements (Format.text " ∧" ++ Format.line)
  let proof := Format.text ("state_run_sound_group [" ++
    ", ".intercalate (members.map (·.defName)) ++ "] [" ++ ", ".intercalate consumers ++ "]")
  -- one declaration proves every relation of the group: the budget a module's preamble
  -- gives one theorem, per relation
  let budget := Format.text s!"set_option maxHeartbeats {4000000 * relations.length} in" ++
    Term.hardLine
  let group := budget ++ Format.text ("theorem " ++ groupSoundName first) ++ ext ++ " :" ++
    Format.nest 4 (Format.line ++ Format.group stmt ++ " := by") ++
    Format.nest 2 (Term.hardLine ++ proof)
  let mut out := [group]
  for (m, i) in relations.zipIdx do
    let (binders, stmt) ← runSoundStatement externs m
    let path := String.join ((List.range i).map fun _ => ".2") ++
      (if relations.length == 1 || i == relations.length - 1 then "" else ".1")
    let outcome := if m.nOuts == 0 then "" else " o"
    let arguments := String.join ((paramNames m.params.length).map (" " ++ ·))
    let term := s!"{qualify (groupSoundName first)}{path}{arguments}{outcome} «@s0» «@sf»"
    out := out ++ [Format.group (Format.nest 4 (Format.text ("theorem " ++ runSoundName m) ++
      binders ++ " :" ++ Format.line ++ stmt ++ " :=")) ++
      Format.nest 2 (Format.line ++ term)]
  -- one audit for the joint theorem and its projections: its proof is traversed once
  let audited := qualify (groupSoundName first) :: relations.map fun m => qualify (runSoundName m)
  pure (out ++ [Format.text "#audit_axioms" ++
    Format.nest 2 (Format.join (audited.map fun name => Term.hardLine ++ Format.text name))])

end P4SpecTec.Codegen.StateProps
