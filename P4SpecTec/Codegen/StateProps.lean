import P4SpecTec.Codegen.Props
import P4SpecTec.Codegen.Rels

/-!
Structural successful rules for the explicit-state backend (not a mirror).
Each selected complete attempt retains the mismatching prefix and its consumed
state. Iteration uses auxiliary mutual predicates and ordered structural chains.
Production selection remains disabled until recursive state run-soundness is proved.
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
  /-- Auxiliary inductives which must enter the enclosing mutual block. -/
  helpers : List Format := []
  /-- Whether the enclosing declarations carry the generated extern interface. -/
  externs : Bool := false

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
      modify fun st => { st with base.hasRel := true }
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
      helperNext := outer.helperNext + 1, externs := outer.externs }
    let (_, inner) ← (translate body).run ctx |>.run init
    let conclusion := (Term.call qualified
      [inputTerm, .atom "«@s0»", result, .atom inner.current]).fmt
    let ctor := closeConstructor "step" inner conclusion
    let ext := if outer.externs then Format.text " [Externs]" else Format.nil
    let decl := Format.text ("inductive " ++ helper) ++ ext ++ " : " ++
      Term.arrows [inputTy.arg, "FreshState", resTy.arg, "FreshState", "Prop"] ++
      " where" ++ Format.nest 2 (Term.hardLine ++ ctor)
    modify fun s => { s with
      helperNext := inner.helperNext
      helpers := s.helpers ++ [decl] ++ inner.helpers }
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
      helperNext := outer.helperNext + 1, externs := outer.externs }
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
      helperNext := inner.helperNext
      helpers := s.helpers ++ [decl] ++ inner.helpers }
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
    (inTypes : List Term)
    (stmts : List Stmt) (outs : List Term) (rejected : List Term) (ret : Term) :
    Except String (Format × List Format) := do
  let inputs := paramNames inTypes.length
  let init : PSt := { base := {
    binders := inputs.zip inTypes ++ [("«@s0»", .atom "FreshState"),
      ("«@s1»", .atom "FreshState")] }, helperPrefix, externs }
  let (_, st) ← (translate stmts).run ctx |>.run init
  -- Earlier attempts have their own lexical scope. Substituting selected-path
  -- temporaries into their rendered bodies would capture their bound locals.
  let applySubsts (f : Format) :=
    st.base.substs.foldl (fun f (n, r) => Props.substFormat n r f) f
  let arguments := inputs.map fun n => Term.raw (applySubsts (Format.text n))
  let closedAttempts := rejected.map fun attempt =>
    let fn := (inputs.zip inTypes).foldr
      (fun (n, ty) body => Term.lamF (Term.binder (Format.text n) ty.fmt) body) attempt
    Term.app fn arguments
  let prefixTy := Term.call "List" [.call "StateEval" [ret]]
  let prefixTerm := Term.ascribe (.list closedAttempts) prefixTy
  let prefixHyp := (Term.call "RejectedPrefix" [prefixTerm, .atom "«@s0»", .atom "«@s1»"]).fmt
  -- Only application arguments and these state indices are free in the prefix;
  -- body-local names must not keep unrelated constructor arguments alive.
  let prefixUses := (Term.tuple (arguments ++ [.atom "«@s0»", .atom "«@s1»"])).fmt
  let conclusion ← (relApp relId (inputs.map Term.atom) outs "«@s0»" st.current).run ctx
    |>.run' init
  pure (closeConstructor name st conclusion [prefixHyp] prefixUses, st.helpers)

/-- State-indexed rules in the exact order of complete executable attempts. -/
def relInductives (ctx : Ctx) (externs : Bool) (id : String) (nottyp : nottyp)
    (inputs : List Nat) (groups : List Lang.Al.rulegroup)
    (elsegroup : Option Lang.Al.elsegroup) : Except String (List Format) := do
  if ctx.env.mode != .freshState then throw "StateProps requires the explicit-state backend"
  let args := (Mixfix.args nottyp.it).map (·.it)
  let (ins, outs) := splitArgs inputs args
  let inTypes := ins.map (typTerm ctx.env [])
  let ret := typTerm.prod (outs.map (typTerm ctx.env []))
  let mut earlier : List Term := []
  let mut ctors : List Format := []
  let mut helpers : List Format := []
  for attempt in Attempt.ofRelation groups elsegroup do
    let (stmts, outs) ← Exp.run ctx (Rels.attemptBlock attempt)
    let k := ctors.length
    let name := if attempt.groupId.it.isEmpty && attempt.pathId.it.isEmpty then s!"rule{k}"
      else Names.ruleName attempt.groupId.it attempt.pathId.it
    let helperPrefix := Names.relName id ++ s!".«@path{k}»"
    let (ctor, extra) ← constructor ctx id name helperPrefix externs inTypes stmts outs earlier ret
    ctors := ctors ++ [ctor]
    helpers := helpers ++ extra
    earlier := earlier ++ [doOfWith .freshState stmts (.tuple outs)]
  let ext := if externs then Format.text " [Externs]" else Format.nil
  let sig := Term.arrows (args.map (fun t => (typTerm ctx.env [] t).arg) ++
    [Format.text "FreshState", Format.text "FreshState", Format.text "Prop"])
  pure ((Format.text ("inductive " ++ Names.relName id) ++ ext ++ " : " ++ sig ++ " where" ++
    Format.nest 2 (Format.join (ctors.map (Term.hardLine ++ ·)))) :: helpers)

/-- Compatibility entry point for a relation that needs no auxiliary mutual predicates. -/
def relInductive (ctx : Ctx) (externs : Bool) (id : String) (nottyp : nottyp)
    (inputs : List Nat) (groups : List Lang.Al.rulegroup)
    (elsegroup : Option Lang.Al.elsegroup) : Except String Format := do
  match ← relInductives ctx externs id nottyp inputs groups elsegroup with
  | [decl] => pure decl
  | _ => throw "stateful structural iteration requires the relInductives mutual-block API"

/-- The exact state-indexed successful result contract of a nonrecursive relation. -/
def runSound (externs : Bool) (m : Props.Member) : Except String Format := do
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
  pure (Format.group (Format.nest 4 (Format.text ("theorem " ++ m.localName ++ "_sound") ++
    ext ++ Props.paramBinders m.params ++ obs ++ states ++ " :" ++ Format.line ++ stmt ++
    " :=")) ++ Format.nest 2 (Format.line ++ "by state_run_sound"))

end P4SpecTec.Codegen.StateProps
