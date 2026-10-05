import P4SpecTec.Codegen.Props
import P4SpecTec.Codegen.Rels

/-!
Structural successful rules for the explicit-state backend (not a mirror).
Each selected complete attempt retains the mismatching prefix and its consumed
state. Iteration uses auxiliary predicates and ordered structural chains. An auxiliary
predicate joins its relation's mutual block only when it mentions a relation of the
recursion group, directly or through a nested auxiliary predicate: Lean's automatic
constructions for a mutual block grow steeply with its number of types, and most iterated
premises call relations defined earlier.
Production planning emits these relations for an explicit-state specification, with a
run-soundness theorem (`Certificates/StateRunSound.lean`) for every relation, a recursion
group jointly.
-/

namespace P4SpecTec.Codegen.StateProps

open Std (Format)
open P4SpecTec.Domain P4SpecTec.Lang.Il P4SpecTec.Lang.Al
open P4SpecTec.Codegen.Types P4SpecTec.Codegen.Exp P4SpecTec.Codegen.Funcs

/-- State indices and the existing path-local variable/substitution bookkeeping. -/
structure PSt where
  /-- Ordinary path variables and structural hypotheses. -/
  base : Props.PSt := {}
  /-- The current state in selected-path execution order. -/
  current : String := "«@s1»"
  /-- The next private state-index name. -/
  next : Nat := 2
  /-- Namespace reserved for this complete attempt's auxiliary predicates. -/
  helperPrefix : String := ""
  /-- Next auxiliary predicate number, shared with nested iterations. -/
  helperNext : Nat := 0
  /-- Auxiliary inductives, outer before nested, each with whether it is tied to the
  recursion group and so must enter the enclosing mutual block. -/
  helpers : List (Bool × Format) := []
  /-- Whether the enclosing declarations carry the generated extern interface. -/
  externs : Bool := false
  /-- The relations of the recursion group being defined. -/
  group : List String := []
  /-- Whether a premise so far mentions a relation of the group, directly or through an
  auxiliary predicate. -/
  tied : Bool := false

/-- Stateful structural translation; this is a compiler monad, not an evaluator. -/
abbrev PM := ReaderT Ctx (StateT PSt (Except String))

/-- Bind a path-local variable. -/
def bindVar (name : String) (ty : Term) : PM Unit :=
  modify fun s => { s with base.binders := s.base.binders ++ [(name, ty)] }

/-- Retain a structural premise or exact executable observation. -/
def hyp (h : Format) : PM Unit :=
  modify fun s => { s with base.hyps := s.base.hyps ++ [h] }

/-- Allocate the next post-state index without changing any semantic state. -/
def advance : PM (String × String) := do
  let st ← get
  let next := s!"«@s{st.next}»"
  bindVar next (.atom "FreshState")
  modify fun s => { s with current := next, next := s.next + 1 }
  pure (st.current, next)

/-- The unchanged notation-order relation arguments, followed by both state indices. -/
def relApp (id : String) (ins outs : List Term) (initial final : String) : PM Format := do
  let ctx ← read
  let base ← (Props.relApp id ins outs).run ctx |>.run' {}
  pure (base ++ " " ++ initial ++ " " ++ final)

/-- An exact successful result and post-state. -/
def someOk (x : Term) (state : String) : Format :=
  Format.text "some (.ok " ++ x.fmt ++ ", " ++ state ++ ")"

/-- Evaluate an explicit-state computation without resetting its supplied state. -/
def runTerm (m : Term) (state : String) : Format :=
  (Term.call "StateEval.run" [m, .atom state]).fmt

/-- Reuse the pure translator for statements that cannot consume state. -/
def pureStmt (stmt : Stmt) : PM Unit := do
  let ctx ← read
  let (_, base) ← (Props.translate [stmt]).run ctx |>.run (← get).base
  modify fun s => { s with base }

/-- Render one structural constructor, closing path-local substitutions and binders. -/
def closeConstructor (name : String) (st : PSt) (conclusion : Format)
    (closedHyps : List Format := []) (closedUses : Format := .nil) : Format := Id.run do
  let applySubsts (f : Format) :=
    st.base.substs.foldl (fun f (n, r) => Props.substFormat n r f) f
  let hyps := st.base.hyps.map applySubsts
  let conclusion := applySubsts conclusion
  let renamed := st.base.binders.map fun (n, t) =>
    (Props.translate.applySubstsName st.base.substs n, t)
  let mut seen : List String := []
  let mut binders : List (String × Term) := []
  for (n, t) in renamed do
    if seen.contains n || !Props.translate.isName n then continue
    if hyps.any (Props.mentions n) || Props.mentions n conclusion ||
        Props.mentions n closedUses then
      binders := binders ++ [(n, t)]
      seen := seen ++ [n]
  let bs := Format.join (binders.map fun (n, t) =>
    Format.line ++ Format.text "{" ++ n ++ " : " ++ t.fmt ++ "}")
  let body := Format.join ((closedHyps ++ hyps).map fun h =>
    Format.paren h ++ " →" ++ Format.line) ++ conclusion
  pure (Format.text ("| " ++ name) ++ Format.nest 4 (Format.group bs ++ " :" ++
    Format.nest 2 (Format.line ++ body)))

/-- Lexical values are indices of auxiliary predicates, never captured predicate parameters. -/
def captures (st : PSt) : List (String × Term) := Id.run do
  let mut seen : List String := []
  let mut result := []
  for (n, t) in st.base.binders do
    let n := Props.translate.applySubstsName st.base.substs n
    if n.startsWith "«@s" || n == "_" || seen.contains n ||
        !Props.translate.isName n then continue
    seen := n :: seen
    result := result ++ [(n, t)]
  pure result

/-- Give captured values private names so an iterator may shadow their source names. -/
def captureBinders (index : Nat) (caps : List (String × Term)) : List (String × Term) :=
  caps.zipIdx.map fun ((_, ty), i) => (s!"«@cap{index}_{i}»", ty)

/-- Freeze outer substitutions in the captured context before entering an iterator scope. -/
def captureSubsts (st : PSt) (caps : List (String × Term)) (shadowed : List String) :
    List (String × Format) := Id.run do
  let renames := caps.zip (captureBinders st.helperNext caps) |>.map fun ((n, _), (c, _)) =>
    (n, Format.text c)
  let inherited := st.base.substs.filterMap fun (n, value) =>
    if shadowed.contains n then none
    else some (n, renames.foldl (fun v (a, b) => Props.substFormat a b v) value)
  pure (inherited ++ renames.filter fun (n, _) => !shadowed.contains n)

/-- Translate a selected attempt in order, retaining every effectful post-state. -/
partial def translate : List Stmt → PM Unit
  | [] => pure ()
  | .call x ty f :: rest => do
    bindVar x ty
    let (s, t) ← advance
    hyp (Props.eqn (f.fmt ++ " " ++ s) (someOk (.atom x) t))
    translate rest
  | .rel x ty rid ins extern m :: rest => do
    let index := (← get).next
    let name := if x == "_" then s!"«@out{index}»" else x
    bindVar name ty
    let (s, t) ← advance
    if extern then
      hyp (Props.eqn (runTerm m s) (someOk (.atom name) t))
    else
      let ctx ← read
      let outs ← (Props.outsOf rid name).run ctx |>.run' {}
      hyp (← relApp rid ins outs s t)
      modify fun st => { st with base.hasRel := true, tied := st.tied || st.group.contains rid }
    translate rest
  | .notHold _ _ _ m :: rest => do
    let (s, t) ← advance
    hyp (Props.eqn (runTerm m s) (Format.text s!"some (.error Fail.unmatch, {t})"))
    translate rest
  | .bind x ty m :: rest => do
    bindVar x ty
    let (s, t) ← advance
    hyp (Props.eqn (runTerm m s) (someOk (.atom x) t))
    translate rest
  | .mapM x resTy _ elems body result z :: rest => do
    let outer ← get
    let ctx ← read
    let caps := captures outer
    let capTerm := Term.tuple (caps.map fun (n, _) => .atom n)
    let locals := captureBinders outer.helperNext caps
    let localTerm := Term.tuple (locals.map fun (n, _) => .atom n)
    let elemTerm := Term.tuple (elems.map fun (n, _) => .atom n)
    let inputTerm := Term.tuple [localTerm, elemTerm]
    let inputTy := tupleType [tupleType (caps.map (·.2)), tupleType (elems.map (·.2))]
    let helper := outer.helperPrefix ++ s!".«@iter{outer.helperNext}»"
    let qualified := ctx.env.q helper
    let init : PSt := {
      base := {
        binders := locals ++ elems ++ [("«@s0»", .atom "FreshState")]
        substs := captureSubsts outer caps (elems.map (·.1)) },
      current := "«@s0»", next := 1, helperPrefix := outer.helperPrefix,
      helperNext := outer.helperNext + 1, externs := outer.externs, group := outer.group }
    let (_, inner) ← (translate body).run ctx |>.run init
    let conclusion := (Term.call qualified
      [inputTerm, .atom "«@s0»", result, .atom inner.current]).fmt
    let ctor := closeConstructor "step" inner conclusion
    let ext := if outer.externs then Format.text " [Externs]" else Format.nil
    let decl := Format.text ("inductive " ++ helper) ++ ext ++ " : " ++
      Term.arrows [inputTy.arg, "FreshState", resTy.arg, "FreshState", "Prop"] ++
      " where" ++ Format.nest 2 (Term.hardLine ++ ctor)
    modify fun s => { s with
      helperNext := inner.helperNext, tied := s.tied || inner.tied
      helpers := s.helpers ++ [(inner.tied, decl)] ++ inner.helpers }
    bindVar x (.call "List" [resTy])
    let (s, t) ← advance
    let tagged := Term.call "List.map"
      [.lamF (Format.text "«@elem»") (.tuple [capTerm, .atom "«@elem»"]), z]
    hyp (Term.call "StateChain" [.atom qualified, tagged, .atom s, .atom x, .atom t]).fmt
    modify fun s => { s with base.hasRel := true }
    translate rest
  | .optM x ty elems body someResult noneResult options :: rest => do
    let outer ← get
    let ctx ← read
    let caps := captures outer
    let capTerm := Term.tuple (caps.map fun (n, _) => .atom n)
    let locals := captureBinders outer.helperNext caps
    let localTerm := Term.tuple (locals.map fun (n, _) => .atom n)
    let someInput := Term.tuple [localTerm,
      .tuple (elems.map fun (n, _) => .call "some" [.atom n])]
    let noneInput := Term.tuple [localTerm, .tuple (elems.map fun _ => .atom "none")]
    let inputTy := tupleType [tupleType (caps.map (·.2)),
      tupleType (elems.map fun (_, t) => .call "Option" [t])]
    let helper := outer.helperPrefix ++ s!".«@optional{outer.helperNext}»"
    let qualified := ctx.env.q helper
    let init : PSt := {
      base := {
        binders := locals ++ elems ++ [("«@s0»", .atom "FreshState")]
        substs := captureSubsts outer caps (elems.map (·.1)) }
      current := "«@s0»", next := 1, helperPrefix := outer.helperPrefix,
      helperNext := outer.helperNext + 1, externs := outer.externs, group := outer.group }
    let (_, inner) ← (translate body).run ctx |>.run init
    let someConclusion := (Term.call qualified
      [someInput, .atom "«@s0»", someResult, .atom inner.current]).fmt
    let noneConclusion := (Term.call qualified
      [noneInput, .atom "«@s0»", noneResult, .atom "«@s0»"]).fmt
    let someCtor := closeConstructor "present" inner someConclusion
    let noneCtor := closeConstructor "absent" init noneConclusion
    let ext := if outer.externs then Format.text " [Externs]" else Format.nil
    let decl := Format.text ("inductive " ++ helper) ++ ext ++ " : " ++
      Term.arrows [inputTy.arg, "FreshState", ty.arg, "FreshState", "Prop"] ++
      " where" ++ Format.nest 2 (Term.hardLine ++ noneCtor ++ Term.hardLine ++ someCtor)
    modify fun s => { s with
      helperNext := inner.helperNext, tied := s.tied || inner.tied
      helpers := s.helpers ++ [(inner.tied, decl)] ++ inner.helpers }
    bindVar x ty
    let (s, t) ← advance
    hyp (Term.call qualified [.tuple [capTerm, .tuple options],
      .atom s, .atom x, .atom t]).fmt
    modify fun s => { s with base.hasRel := true }
    translate rest
  | stmt :: rest => do
    pureStmt stmt
    translate rest

/-- Render a named structural path constructor from its retained hypotheses. -/
def constructor (ctx : Ctx) (relId name helperPrefix : String) (externs : Bool)
    (group : List String) (inTypes : List Term)
    (stmts : List Stmt) (outs : List Term) (rejected : List Term) (ret : Term) :
    Except String (Format × List (Bool × Format)) := do
  let inputs := paramNames inTypes.length
  let init : PSt := { base := {
    binders := inputs.zip inTypes ++ [("«@s0»", .atom "FreshState"),
      ("«@s1»", .atom "FreshState")] }, helperPrefix, externs, group }
  let (_, st) ← (translate stmts).run ctx |>.run init
  -- Earlier attempts have their own lexical scope: each is a named definition of the
  -- relation's inputs, applied here to the selected path's input patterns. Restating its
  -- body in every later constructor would make a relation's text quadratic in its rules.
  let applySubsts (f : Format) :=
    st.base.substs.foldl (fun f (n, r) => Props.substFormat n r f) f
  let arguments := inputs.map fun n => Term.raw (applySubsts (Format.text n))
  let closedAttempts := rejected.map fun attempt => Term.app attempt arguments
  let prefixTy := Term.call "List" [.call "StateEval" [ret]]
  let prefixTerm := Term.ascribe (.list closedAttempts) prefixTy
  let prefixHyp := (Term.call "RejectedPrefix" [prefixTerm, .atom "«@s0»", .atom "«@s1»"]).fmt
  -- Only application arguments and these state indices are free in the prefix;
  -- body-local names must not keep unrelated constructor arguments alive.
  let prefixUses := (Term.tuple (arguments ++ [.atom "«@s0»", .atom "«@s1»"])).fmt
  let conclusion ← (relApp relId (inputs.map Term.atom) outs "«@s0»" st.current).run ctx
    |>.run' init
  pure (closeConstructor name st conclusion [prefixHyp] prefixUses, st.helpers)

/-- The name of a relation's complete attempt, as a definition of its inputs. -/
def attemptName (id : String) (k : Nat) : String := Names.relName id ++ s!".«@attempt{k}»"

/-- A relation's structural predicates. -/
structure Inductives where
  /-- Every complete attempt but the last as a reducible definition of the relation's
  inputs: the computation a later constructor's rejected prefix refers to. They call the
  executable definitions only, so they precede every predicate. -/
  attempts : List Format
  /-- The relation itself, one constructor per complete attempt. -/
  relation : Format
  /-- Auxiliary predicates that mention a relation of the recursion group. -/
  tied : List Format
  /-- Auxiliary predicates that mention none, nested ones first: each is declared on its
  own, ahead of the group's mutual block. -/
  free : List Format

/-- The declarations of a recursion group's relations: the independent auxiliary
predicates, then one mutual block of the relations and the predicates tied to them. -/
def Inductives.declarations (group : List Inductives) : Format :=
  joinDecls (group.flatMap (·.attempts) ++ group.flatMap (·.free) ++
    [mutualBlock (group.map (·.relation) ++ group.flatMap (·.tied))])

/-- State-indexed rules in the exact order of complete executable attempts. `group` names
the relations of the recursion group, the relation itself included. -/
def relInductives (ctx : Ctx) (externs : Bool) (id : String) (nottyp : nottyp)
    (inputs : List Nat) (groups : List Lang.Al.rulegroup)
    (elsegroup : Option Lang.Al.elsegroup) (group : List String := [id]) :
    Except String Inductives := do
  if ctx.env.mode != .freshState then throw "StateProps requires the explicit-state backend"
  let args := (Mixfix.args nottyp.it).map (·.it)
  let (ins, outs) := splitArgs inputs args
  let inTypes := ins.map (typTerm ctx.env [])
  let ret := typTerm.prod (outs.map (typTerm ctx.env []))
  let mut earlier : List Term := []
  let mut definitions : List Format := []
  let mut ctors : List Format := []
  let mut helpers : List (Bool × Format) := []
  let ext := if externs then Format.text " [Externs]" else Format.nil
  let inputBinders := Format.join (((paramNames inTypes.length).zip inTypes).map fun (n, ty) =>
    Format.line ++ Format.paren (Format.text (n ++ " : ") ++ ty.fmt))
  let attempts := Attempt.ofRelation groups elsegroup
  let names := Names.ruleNames (attempts.map fun a => (a.groupId.it, a.pathId.it))
  for attempt in attempts do
    let (stmts, outs) ← Exp.run ctx (Rels.attemptBlock attempt)
    let k := ctors.length
    let name := names.getD k s!"rule{k}"
    let helperPrefix := Names.relName id ++ s!".«@path{k}»"
    let (ctor, extra) ←
      constructor ctx id name helperPrefix externs group inTypes stmts outs earlier ret
    ctors := ctors ++ [ctor]
    helpers := helpers ++ extra
    if k + 1 < attempts.length then
      definitions := definitions ++ [Format.text "@[reducible] def " ++ attemptName id k ++ ext ++
        Format.group (Format.nest 4 inputBinders) ++ " : StateEval " ++ ret.arg ++ " :=" ++
        Format.nest 2 (Format.line ++ (doOfWith .freshState stmts (.tuple outs)).fmt)]
      earlier := earlier ++ [.atom (ctx.env.q (attemptName id k))]
  let sig := Term.arrows (args.map (fun t => (typTerm ctx.env [] t).arg) ++
    [Format.text "FreshState", Format.text "FreshState", Format.text "Prop"])
  let relation := Format.text ("inductive " ++ Names.relName id) ++ ext ++ " : " ++ sig ++
    " where" ++ Format.nest 2 (Format.join (ctors.map (Term.hardLine ++ ·)))
  -- an outer predicate precedes the ones nested in it: declare the independent ones in
  -- reverse, so that each follows what it mentions
  pure { attempts := definitions, relation, tied := (helpers.filter (·.1)).map (·.2)
         free := ((helpers.filter (!·.1)).map (·.2)).reverse }

/-- Compatibility entry point for a relation that needs no auxiliary predicates. -/
def relInductive (ctx : Ctx) (externs : Bool) (id : String) (nottyp : nottyp)
    (inputs : List Nat) (groups : List Lang.Al.rulegroup)
    (elsegroup : Option Lang.Al.elsegroup) : Except String Format := do
  match ← relInductives ctx externs id nottyp inputs groups elsegroup with
  | { attempts := [], relation, tied := [], free := [] } => pure relation
  | _ => throw "stateful structural iteration requires the relInductives declarations API"

end P4SpecTec.Codegen.StateProps
