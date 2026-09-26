import P4SpecTec.Codegen.Props

/-!
Run-soundness and determinism theorem emission for generated relation groups.

The existing `Codegen.Props` names are retained for callers and certificate metadata.
-/

namespace P4SpecTec.Codegen.Props

open Std (Format)
open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al
open P4SpecTec.Codegen.Types
open P4SpecTec.Codegen.Exp
open P4SpecTec.Codegen.Funcs

/-! ## Run-soundness theorems -/

/-- What the theorem generator knows about a group member. -/
structure Member where
  /-- The spec id. -/
  id : String
  /-- Whether it is a relation (else a function or table). -/
  isRel : Bool
  /-- The qualified Lean name of the definition (`Lib.R.run` or `Lib.«$f»`),
  for references. -/
  defName : String
  /-- The unqualified name (`R.run`, `«$f»`), for declarations inside the
  library's namespace. -/
  localName : String
  /-- The parameter types. -/
  params : List Term
  /-- The result type inside `Option (Except Fail _)`. -/
  ret : Term
  /-- For a relation: the number of outputs. -/
  nOuts : Nat := 0
  /-- For a relation: the relation applied to inputs `p_i` and the outputs
  named `o` (one) or `o.1, o.2, ...` (several), in notation order. -/
  conclusion : Format := Format.nil
  /-- The relation applied to inputs and outputs named `o0, o1, ...`. -/
  conclusionNamed : Format := Format.nil
  /-- The output types. -/
  outTypes : List Term := []
  /-- For a relation: why no determinism theorem is attempted (one rule
  path, no recursion, no iterated premise are required), or `none`. -/
  detReason : Option String := some "not a relation"
  deriving Inhabited

/-- The binders `(p0 : T0) (p1 : T1)` of the parameters, each after a
break point. -/
def paramBinders (ps : List Term) : Format :=
  Format.join ((paramNames ps.length).zip ps |>.map fun (n, t) =>
    Format.line ++ Format.text "(" ++ n ++ " : " ++ t.fmt ++ ")")

/-- The motive statement of a member for `partial_correctness`:
`∀ params r, f params = some r → ∀ o, r = .ok o → R ... o` for a relation,
`True` for a function. -/
def motiveStmt (m : Member) : Format :=
  let ps := paramNames m.params.length
  let call := (Term.call m.defName (ps.map Term.atom)).fmt
  let head := Format.text "∀" ++ paramBinders m.params ++ Format.line ++ "(r : Except Fail " ++
    m.ret.arg ++ ")," ++ Format.line ++ call ++ " = some r →"
  if m.isRel then
    Format.group (Format.nest 4 (head ++ Format.line ++ "∀ (o : " ++ m.ret.fmt ++
      "), r = .ok o →" ++ Format.line ++ m.conclusion))
  else Format.group (Format.nest 4 (head ++ Format.line ++ "True"))

/-- Shared binders and conclusion of a relation's run-soundness corollary. -/
private def corollaryParts (externs : Bool) (m : Member) : Format × Format :=
  let ps := paramNames m.params.length
  let ext := if externs then Format.text " [Externs]" else Format.nil
  -- the outputs as one variable `o` (a tuple for several), so that the
  -- theorem applies to a call whose result is not yet destructured
  let obs := if m.nOuts == 0 then Format.nil
    else Format.line ++ Format.text "(o : " ++ m.ret.fmt ++ ")"
  let outArg := if m.nOuts == 0 then "()" else "o"
  let call := (Term.call m.defName (ps.map Term.atom)).fmt
  let stmt := Format.group (Format.nest 4 (
    call ++ " = " ++ someOk (.atom outArg) ++ " →" ++ Format.line ++ m.conclusion))
  (ext ++ paramBinders m.params ++ obs, stmt)

/-- The closed type of the emitted per-relation `R.run_sound` theorem,
including its optional extern instance and explicit input/output binders. -/
def corollaryType (externs : Bool) (m : Member) : Format :=
  let (bs, stmt) := corollaryParts externs m
  if !externs && m.params.isEmpty && m.nOuts == 0 then stmt
  else Format.group (Format.nest 4 (Format.text "∀" ++ bs ++ "," ++ Format.line ++ stmt))

/-- The corollary `R.run_sound` of a relation from the group theorem
`thm` (a projection path into its conjunction), or `none` to prove it
directly by `run_sound` when the group is not recursive. -/
def corollary (externs : Bool) (m : Member) (thm : Option String) : Format :=
  let ps := paramNames m.params.length
  let outArg := if m.nOuts == 0 then "()" else "o"
  let (bs, stmt) := corollaryParts externs m
  let header := Format.group (Format.nest 4 (Format.text ("theorem " ++ m.localName ++ "_sound") ++
    bs ++ " :" ++ Format.line ++ stmt ++ " :="))
  match thm with
  | some t =>
    header ++ Format.nest 2 (Format.line ++ Format.text ("fun h => " ++ t ++ " " ++
      " ".intercalate ps ++ " _ h " ++ outArg ++ " rfl"))
  | none => header ++ Format.nest 2 (Format.line ++ "by run_sound")

/-- The axiom audit of a theorem. -/
def audit (name : String) : Format := Format.text ("#audit_axioms " ++ name)

/-- Shared binders and conclusion of a relation's determinism theorem. -/
private def detTheoremParts (externs : Bool) (m : Member) : Format × Format :=
  let ps := paramNames m.params.length
  let ext := if externs then Format.text " [Externs]" else Format.nil
  let n := m.nOuts
  let outs := (List.range n).map fun k => s!"o{k}"
  let outs' := (List.range n).map fun k => s!"o{k}'"
  -- implicit: the theorem is applied to the two derivations directly
  let obs := Format.join ((outs.zip outs' |>.zip m.outTypes).map fun ((o, o'), t) =>
    Format.line ++ Format.text s!"\{{o} {o'} : " ++ t.fmt ++ "}")
  let ins := Format.join ((ps.zip m.params).map fun (n, t) =>
    Format.line ++ Format.text ("{" ++ n ++ " : ") ++ t.fmt ++ "}")
  let rel := m.defName.replace ".run" ""
  let app (os : List String) := (Term.call rel ((ps ++ os).map Term.atom)).fmt
  let eqs := if n == 0 then Format.text "True"
    else Format.joinSep ((outs.zip outs').map fun (o, o') => Format.text s!"{o} = {o'}")
      (Format.text " ∧" ++ Format.line)
  let stmt := Format.group (Format.nest 4 (app outs ++ " →" ++ Format.line ++ app outs' ++ " →" ++
    Format.line ++ eqs))
  (ext ++ ins ++ obs, stmt)

/-- The closed type of the emitted per-relation `R.det` theorem,
including its optional extern instance and implicit input/output binders. -/
def detTheoremType (externs : Bool) (m : Member) : Format :=
  let (bs, stmt) := detTheoremParts externs m
  if !externs && m.params.isEmpty && m.nOuts == 0 then stmt
  else Format.group (Format.nest 4 (Format.text "∀" ++ bs ++ "," ++ Format.line ++ stmt))

/-- The determinism theorem `R.det` of a relation:
`R ins outs → R ins outs' → outs = outs'`, by `det`. -/
def detTheorem (externs : Bool) (m : Member) : Format :=
  let (bs, stmt) := detTheoremParts externs m
  let name := m.localName.replace ".run" "" ++ ".det"
  Format.group (Format.nest 4 (Format.text ("theorem " ++ name) ++
    bs ++ " :" ++ Format.line ++ stmt ++ " :=")) ++
    Format.nest 2 (Format.line ++ "by det")

/-- The theorems of a group: the group theorem by `partial_correctness`
when the group is recursive, and one corollary per relation. -/
def groupTheorems (externs recursive : Bool) (members : List Member) : List Format := Id.run do
  let rels := members.filter (·.isRel)
  if rels.isEmpty then return []
  let ext := if externs then Format.text " [Externs]" else Format.nil
  let mut out : List Format := []
  if !recursive then
    for m in rels do
      out := out ++ [corollary externs m none, audit (m.defName ++ "_sound")]
      match m.detReason with
      | none => out := out ++ [detTheorem externs m, audit (m.defName.replace ".run" "" ++ ".det")]
      | some r => out := out ++ [Format.text s!"-- no determinism theorem: {m.id}\n--   {r}"]
    return out
  let first := members.head!
  let groupName := first.defName ++ "_sound_group"
  let principle := if members.length == 1 then first.defName ++ ".partial_correctness"
    else first.defName ++ ".mutual_partial_correctness"
  let stmt := Format.joinSep (members.map fun m => Format.paren (motiveStmt m))
    (Format.text " ∧" ++ Format.line)
  let proof := Format.text ("run_sound_group " ++ principle)
  out := out ++ [Format.text ("theorem " ++ first.localName ++ "_sound_group") ++ ext ++ " :" ++
    Format.nest 4 (Format.line ++ Format.group stmt ++ " := by") ++
    Format.nest 2 (Term.hardLine ++ proof), audit groupName]
  for (m, i) in members.zipIdx do
    if !m.isRel then continue
    let proj := if members.length == 1 then groupName
      else groupName ++ String.join ((List.range i).map fun _ => ".2") ++
        (if i == members.length - 1 then "" else ".1")
    out := out ++ [corollary externs m (some proj), audit (m.defName ++ "_sound")]
  pure out

/-- A member from a definition. -/
def memberOf (ctx : Ctx) (d : Lang.Al.def) : Except String Member := do
  let env := ctx.env
  match d.it with
  | .RelD i nottyp inputs groups eg _ =>
    let args := (Mixfix.args nottyp.it).map (·.it)
    let (ins, outs) := splitArgs (inputs.map (·.toNat)) args
    let inTypes := ins.map (typTerm env [])
    let outTypes := outs.map (typTerm env [])
    let ps := paramNames ins.length
    let n := outs.length
    let outsProj := match n with
      | 0 => []
      | 1 => [Term.atom "o"]
      | n => (projections n).map fun p => Term.atom ("o" ++ p)
    let outsNamed := (List.range n).map fun k => Term.atom s!"o{k}"
    let concl ← (relApp i.it (ps.map Term.atom) outsProj).run ctx |>.run' {}
    let conclNamed ← (relApp i.it (ps.map Term.atom) outsNamed).run ctx |>.run' {}
    -- determinism is attempted on one rule path without iteration; a
    -- second path can overlap the first, and an iterated premise needs
    -- an induction the tactic does not do
    let paths := (groups.map fun g => let (_, _, ps) := g.it; ps.length).sum
    let prems := groups.flatMap (fun g =>
      let (_, (_, _, ps), paths) := g.it
      ps ++ paths.flatMap fun (_, ps, _) => ps) ++ (match eg with
      | some e => let (_, (_, _, ps), (_, ps', _)) := e.it; ps ++ ps'
      | none => [])
    let iterated := prems.any fun p => match p.it with | .IterPr .. => true | _ => false
    let detReason := if eg.isSome then some "else group"
      else if paths != 1 then some s!"{paths} rule paths"
      else if iterated then some "iterated premise"
      else none
    pure (Member.mk i.it true (env.q (Names.relName i.it ++ ".run")) (Names.relName i.it ++ ".run")
      inTypes (typTerm.prod outTypes) n concl conclNamed outTypes detReason)
  | .FuncDecD i _ params ret _ _ _ | .BuiltinDecD i _ params ret _ | .TableDecD i params ret _ _ =>
    pure (Member.mk i.it false (env.q (Names.funcName i.it)) (Names.funcName i.it)
      ((paramTypes (params.map (·.it))).map (typTerm env [])) (typTerm env [] ret.it) 0
      Format.nil Format.nil [] (some "not a relation"))
  | _ => throw s!"not a function or relation: {d.it.id.it}"

end P4SpecTec.Codegen.Props
