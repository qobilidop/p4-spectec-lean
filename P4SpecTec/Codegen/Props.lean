import P4SpecTec.Codegen.Rels

/-!
Relations, `Prop` encoding: `RelD` to an inductive `R : args → Prop` with
one constructor per rule path, and the run-soundness theorems linking it
to the executable encoding (`R.run i = some (.ok o) → R i o`; design
section 4.1). Both encodings come from one compilation of the rule
paths: the statements `Exp` produces for the run function are read here
as hypotheses, in the same A-normal form, so that the tactic `run_sound`
(`P4SpecTec/Tactic/RunSound.lean`) can close every theorem by executing
the run function symbolically against the constructor.

The encoding of a rule path (design section 5.4):

- Every variable the path binds (rule inputs, pattern variables and the
  temporaries of hoisted calls) is an implicit constructor argument with
  its type; the conclusion is the relation applied to its arguments in
  notation order, with the input patterns substituted.
- A hoisted call is the hypothesis `f args = some (.ok x)`; a hoisted
  partial operation `o = some x`; an `if` premise `e = true`; a rule
  premise the relation applied to inputs and outputs; a `holds` premise
  the relation applied to its arguments; a `does not hold` premise
  `R'.run args = some (.error Fail.unmatch)`, since the negation of a
  relation cannot occur in its own definition (deviation, design 5.3).
- A pure binding `have x := e` is substituted (as `do` does), and a
  pattern binding substitutes the pattern for the matched variable.
- An iterated premise over the zipped lists `z` collecting `x` is the
  length hypothesis `z.length = x.length` and a pointwise hypothesis
  `∀ elems y, (elems, y) ∈ List.zip z x → ...`: the relation-free facts of
  the premise under `∃` for their temporaries, and every relation fact as
  an implication from those facts, because the kernel rejects a relation
  under `∃`, `∧` or `∨` inside its own constructors.
- An `else` group carries no negation of the other groups (deviation).
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

/-! ## Substitution in rendered text -/

/-- Whether a character continues an identifier. -/
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'

/-- Replace every whole-identifier occurrence of `name` in `s` by `rep`,
splitting the text around it. An occurrence preceded by an identifier
character or a dot (a namespace or projection component) is left alone. -/
partial def substText (name : String) (rep : Format) (s : String) : Format := Id.run do
  let cs := s.toList
  let n := name.toList
  let mut out : Format := Format.nil
  let mut acc : List Char := []
  let mut rest := cs
  let mut prev : Option Char := none
  while !rest.isEmpty do
    let after := rest.drop n.length
    let ok := rest.take n.length == n &&
      (match prev with
        | some '«' => after.head? == some '»'   -- inside «»: the whole token
        | some c => !(isIdChar c || c == '.')
        | none => true) &&
      (match after with | c :: _ => !isIdChar c || prev == some '«' | [] => true)
    if ok then
      out := out ++ Format.text (String.ofList acc.reverse) ++ rep
      acc := []
      rest := rest.drop n.length
      prev := n.getLast?
    else
      match rest with
      | c :: cs' =>
        acc := c :: acc
        rest := cs'
        prev := some c
      | [] => pure ()
  pure (out ++ Format.text (String.ofList acc.reverse))

/-- Substitute in a format. -/
partial def substFormat (name : String) (rep : Format) : Format → Format
  | .text s => substText name rep s
  | .nest n f => .nest n (substFormat name rep f)
  | .append f g => .append (substFormat name rep f) (substFormat name rep g)
  | .group f b => .group (substFormat name rep f) b
  | .tag n f => .tag n (substFormat name rep f)
  | f => f

/-- Whether `name` occurs as a whole identifier in a rendered format. -/
def mentions (name : String) (f : Format) : Bool :=
  let s := render f
  let marked := render (substText name (Format.text "\u0001") s)
  marked != s

/-! ## The hypotheses of a rule path -/

/-- The state of one path's translation. -/
structure PSt where
  /-- Variables bound so far, with their types, in order. -/
  binders : List (String × Term) := []
  /-- The hypotheses so far. -/
  hyps : List Format := []
  /-- Substitutions to apply, in order, to every binder name, hypothesis and
  the conclusion: renamings (`have x := tmp`, an input alias) and pattern
  substitutions. -/
  substs : List (String × Format) := []
  /-- Whether a relation fact was emitted (for inner scopes). -/
  hasRel : Bool := false

/-- The translation monad: the codegen context and the path state. -/
abbrev PM := ReaderT Ctx (StateT PSt (Except String))

/-- Bind a variable. -/
def bindVar (x : String) (ty : Term) : PM Unit :=
  modify fun st => { st with binders := st.binders ++ [(x, ty)] }

/-- Add a hypothesis. -/
def hyp (f : Format) : PM Unit := modify fun st => { st with hyps := st.hyps ++ [f] }

/-- Add a substitution, its replacement closed under the earlier ones, so
that applying the list in order substitutes every variable once. -/
def subst (x : String) (rep : Format) : PM Unit :=
  modify fun st =>
    let rep := st.substs.foldl (fun f (n, r) => substFormat n r f) rep
    { st with substs := st.substs ++ [(x, rep)] }

/-- The type of a bound variable, if known. -/
def typeOfVar (x : String) : PM (Option Term) := do
  pure ((← get).binders.lookup x)

/-- `some (.ok x)`. -/
def someOk (x : Term) : Format := Format.text "some (.ok " ++ x.fmt ++ ")"

/-- The equation `lhs = rhs`. -/
def eqn (lhs : Format) (rhs : Format) : Format :=
  Format.group (Format.nest 2 (lhs ++ " =" ++ Format.line ++ rhs))

/-- The relation `id` applied to its arguments in notation order: the
inputs and outputs interleaved as the input hint says. -/
def relApp (id : String) (ins : List Term) (outs : List Term) : PM Format := do
  let ctx ← read
  match ctx.env.rels.get? id with
  | some info =>
    let mut args : List Term := []
    let mut ins := ins
    let mut outs := outs
    for i in List.range info.args.length do
      if info.inputs.contains i then
        match ins with
        | a :: rest => args := args ++ [a]; ins := rest
        | [] => throw s!"relation {id}: too few inputs"
      else
        match outs with
        | a :: rest => args := args ++ [a]; outs := rest
        | [] => throw s!"relation {id}: too few outputs"
    pure (Term.call (ctx.env.q (Names.relName id)) args).fmt
  | none => throw s!"unknown relation {id}"

/-- The output terms of a relation from the variable `x` holding its output
tuple: `x` itself for one output, projections for several. -/
def outsOf (id : String) (x : String) : PM (List Term) := do
  let ctx ← read
  match ctx.env.rels.get? id with
  | some info =>
    let (_, outs) := splitArgs info.inputs info.args
    match outs.length with
    | 0 => pure []
    | 1 => pure [.atom x]
    | n => pure ((projections n).map fun p => Term.atom (x ++ p))
  | none => throw s!"unknown relation {id}"

/-- The rendered call of an extern relation's field. -/
def externCall (id : String) (ins : List Term) : PM Format := do
  let ctx ← read
  pure (Term.call (ctx.env.q ("Externs." ++ Names.relName id)) ins).fmt

/-- Translate the statements of a path in order. -/
partial def translate : List Stmt → PM Unit
  | [] => pure ()
  | .call x ty f :: rest => do
    bindVar x ty
    hyp (eqn f.fmt (someOk (.atom x)))
    translate rest
  | .opt x ty o :: rest => do
    bindVar x ty
    hyp (eqn o.fmt (Format.text "some " ++ (Term.atom x).arg))
    translate rest
  | .rel x ty rid ins extern _ :: rest => do
    if extern then
      if x == "_" then
        hyp (Format.text "∃ u, " ++ eqn (← externCall rid ins) (someOk (.atom "u")))
      else
        bindVar x ty
        hyp (eqn (← externCall rid ins) (someOk (.atom x)))
      translate rest
    else
      modify fun st => { st with hasRel := true }
      if x == "_" then
        hyp (← relApp rid ins [])
        translate rest
      else
        -- the outputs: the tuple pattern the generator binds right after,
        -- else the variable (with projections for several outputs)
        match rest with
        | .letPat _ _ vars (.atom v) false :: rest' =>
          if v == x && vars.length > 1 then
            for (n, t) in vars do bindVar n t
            hyp (← relApp rid ins (vars.map fun (n, _) => Term.atom n))
            translate rest'
          else
            bindVar x ty
            hyp (← relApp rid ins (← outsOf rid x))
            translate rest
        | _ =>
          bindVar x ty
          hyp (← relApp rid ins (← outsOf rid x))
          translate rest
  | .notHold rid ins extern _ :: rest => do
    let ctx ← read
    let call ← if extern then externCall rid ins
      else pure (Term.call (ctx.env.q (Names.relName rid ++ ".run")) ins).fmt
    hyp (eqn call (Format.text "some (.error Fail.unmatch)"))
    translate rest
  | .check b :: rest => do
    -- ascribed, so that `||` and `==` elaborate as `Bool`, as in the run function
    hyp (eqn (Term.ascribe b (.atom "Bool")).fmt (Format.text "true"))
    translate rest
  | .have_ x v :: rest => do
    match v with
    | ⟨.text s, true⟩ =>
      -- an alias of a variable: rename the variable to the spec name
      match ← typeOfVar s with
      | some ty => bindVar x ty
      | none => pure ()
      subst s (Format.text x)
    | _ => subst x (Format.paren v.fmt)
    translate rest
  | .letPat _ patTerm vars v _ :: rest => do
    for (n, t) in vars do bindVar n t
    match v with
    | ⟨.text s, true⟩ => subst s patTerm.arg
    | _ => hyp (eqn v.fmt patTerm.fmt)
    translate rest
  | .mapM x resTy _ elems body result z :: rest => do
    bindVar x (.call "List" [resTy])
    hyp (eqn (Term.call "List.length" [z]).fmt (Term.call "List.length" [.atom x]).fmt)
    -- the pointwise facts, in a fresh inner scope
    let ctx ← read
    let ((), st) ← match (translate body).run ctx |>.run { binders := [] } with
      | .ok r => pure r
      | .error e => throw e
    let applySubsts (f : Format) : Format :=
      st.substs.foldl (fun f (n, r) => substFormat n r f) f
    let hyps := st.hyps.map applySubsts
    -- the element pattern and the collected pattern: the elements and the
    -- result after the inner substitutions; their variables are ∀-bound
    let pat := zipPattern (elems.map fun (n, _) => applySubsts (Format.text n))
    let collected := applySubsts result.fmt
    let mem := Format.text "(" ++ pat ++ ", " ++ collected ++ ") ∈ " ++
      (Term.call "List.zip" [z, .atom x]).arg
    let renamed := st.binders.map fun (n, t) => (applySubstsName st.substs n, t)
    let mut foralls : List (String × Term) := []
    for (n, t) in elems do
      if mentions n mem && !foralls.any (·.1 == n) then foralls := foralls ++ [(n, t)]
    for (n, t) in renamed do
      if isName n && mentions n mem && !foralls.any (·.1 == n) then foralls := foralls ++ [(n, t)]
    let mut temps : List (String × Term) := []
    for (n, t) in renamed do
      if isName n && !foralls.any (·.1 == n) && !temps.any (·.1 == n) &&
          hyps.any (mentions n) then
        temps := temps ++ [(n, t)]
    let binderF (l : List (String × Term)) : Format := Format.join (l.map fun (n, t) =>
      Format.line ++ Format.text "(" ++ n ++ " : " ++ t.fmt ++ ")")
    let isRel (f : Format) : Bool :=
      (relIds ctx).any fun r => mentions (ctx.env.q (Names.relName r)) f
    let free := hyps.filter (!isRel ·)
    let rels := hyps.filter isRel
    let conj (fs : List Format) : Format :=
      Format.joinSep fs (Format.text " ∧" ++ Format.line)
    let head := Format.text "∀" ++ binderF foralls ++ "," ++ Format.line ++ mem ++ " →"
    -- the relation-free facts, with their temporaries under ∃
    unless free.isEmpty do
      let body := if temps.isEmpty then conj free
        else Format.text "∃" ++ binderF temps ++ "," ++ Format.line ++ conj free
      hyp (Format.group (Format.nest 2 (head ++ Format.line ++ body)))
    -- every relation fact as an implication from those facts
    for r in rels do
      let foralls' := if temps.isEmpty then Format.nil
        else Format.text " ∀" ++ binderF temps ++ ","
      let ants := Format.join (free.map fun f => f ++ " →" ++ Format.line)
      hyp (Format.group (Format.nest 2 (head ++ foralls' ++ Format.line ++ ants ++ r)))
    translate rest
  | .bind x ty m :: rest => do
    bindVar x ty
    hyp (eqn (Format.text "ExceptT.run " ++ m.arg) (someOk (.atom x)))
    translate rest
where
  /-- The zipped pattern of element patterns, nested as `zipped` nests. -/
  zipPattern : List Format → Format
    | [] => Format.text "_"
    | [n] => n
    | n :: ns => Format.text "(" ++ n ++ ", " ++ zipPattern ns ++ ")"
  /-- Whether a binder name is a name (plain or `«»`-quoted), not a term a
  substitution produced. -/
  isName (n : String) : Bool :=
    Names.isPlainIdent n || (n.startsWith "«" && n.endsWith "»" && (n.splitOn "«").length == 2)
  /-- The defined relations of the spec. -/
  relIds (ctx : Ctx) : List String := ctx.env.rels.toList.filterMap fun (rid, info) =>
    if info.extern then none else some rid
  /-- A binder name after the renamings. -/
  applySubstsName (substs : List (String × Format)) (n : String) : String :=
    substs.foldl (fun n (a, r) => if n == a then render r else n) n

/-- The constructor of one rule path. -/
def pathCtor (ctx : Ctx) (relId : String) (name : String) (nInputs : Nat)
    (inTypes : List Term) (stmts : List Stmt) (outs : List Term) : Except String Format := do
  let inputs := paramNames nInputs
  let init : PSt := { binders := inputs.zip inTypes }
  let ((), st) ← (translate stmts).run ctx |>.run init
  let applySubsts (f : Format) : Format := st.substs.foldl (fun f (n, r) => substFormat n r f) f
  let hyps := st.hyps.map applySubsts
  let conclusion ← (relApp relId (inputs.map Term.atom) outs).run ctx |>.run' init
  let conclusion := applySubsts conclusion
  -- the binders that survive the substitutions, renamed
  let renamed := st.binders.map fun (n, t) =>
    (st.substs.foldl (fun n (a, r) => if n == a then render r else n) n, t)
  let mut seen : List String := []
  let mut binders : List (String × Term) := []
  for (n, t) in renamed do
    if seen.contains n || !translate.isName n then continue
    if hyps.any (mentions n) || mentions n conclusion then
      binders := binders ++ [(n, t)]
      seen := seen ++ [n]
  let bs := Format.join (binders.map fun (n, t) =>
    Format.line ++ Format.text "{" ++ n ++ " : " ++ t.fmt ++ "}")
  -- every hypothesis parenthesised: a `∀` would otherwise extend over the rest
  let body := Format.join (hyps.map fun h => Format.paren h ++ " →" ++ Format.line) ++ conclusion
  pure (Format.text ("| " ++ name) ++ Format.nest 4 (Format.group bs ++ " :" ++
    Format.nest 2 (Format.line ++ body)))

/-- The rule paths of a relation as constructors. -/
def relCtors (ctx : Ctx) (id : String) (nottyp : nottyp) (inputs : List Nat)
    (groups : List Lang.Al.rulegroup) (elsegroup : Option Lang.Al.elsegroup) :
    Except String (List Format) := do
  let args := (Mixfix.args nottyp.it).map (·.it)
  let (ins, _) := splitArgs inputs args
  let inTypes := ins.map (typTerm ctx.env [])
  let path (k : Nat) (gid : String) (m : rulematch) (p : rulepath) : Except String Format := do
    let (_, matchIns, prems) := m
    let (pid, pprems, outs) := p
    -- an unnamed rule (upstream allows it) is named by its position
    let name := if gid.isEmpty && pid.it.isEmpty then s!"rule{k}" else Names.ruleName gid pid.it
    let ((stmts, outTerms)) ← Exp.run ctx do
      let ((), stmts) ← subBlock do
        for (e, n) in matchIns.zip (paramNames matchIns.length) do assign e (.atom n)
        for q in prems do compilePrem q
        for q in pprems do compilePrem q
      let (outTerms, stmts2) ← subBlock (outs.mapM compileExp)
      pure (stmts ++ stmts2, outTerms)
    pathCtor ctx id name ins.length inTypes stmts outTerms
  let mut ctors : List Format := []
  for g in groups do
    let (gid, m, paths) := g.it
    for p in paths do ctors := ctors ++ [← path ctors.length gid.it m p]
  if let some e := elsegroup then
    let (gid, m, p) := e.it
    ctors := ctors ++ [← path ctors.length gid.it m p]
  pure ctors

/-- The inductive of one relation (the body of a `mutual` block when the
group has several). -/
def relInductive (ctx : Ctx) (externs : Bool) (id : String) (nottyp : nottyp)
    (inputs : List Nat) (groups : List Lang.Al.rulegroup)
    (elsegroup : Option Lang.Al.elsegroup) : Except String Format := do
  let args := (Mixfix.args nottyp.it).map (·.it)
  let ctors ← relCtors ctx id nottyp inputs groups elsegroup
  let ext := if externs then Format.text " [Externs]" else Format.nil
  let sig := Term.arrows (args.map (fun t => (typTerm ctx.env [] t).arg) ++ [Format.text "Prop"])
  pure (Format.text ("inductive " ++ Names.relName id) ++ ext ++ " : " ++ sig ++ " where" ++
    Format.nest 2 (Format.join (ctors.map (Term.hardLine ++ ·))))

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

/-- The corollary `R.run_sound` of a relation from the group theorem
`thm` (a projection path into its conjunction), or `none` to prove it
directly by `run_sound` when the group is not recursive. -/
def corollary (externs : Bool) (m : Member) (thm : Option String) : Format :=
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
  let header := Format.group (Format.nest 4 (Format.text ("theorem " ++ m.localName ++ "_sound") ++
    ext ++ paramBinders m.params ++ obs ++ " :" ++ Format.line ++ stmt ++ " :="))
  match thm with
  | some t =>
    header ++ Format.nest 2 (Format.line ++ Format.text ("fun h => " ++ t ++ " " ++
      " ".intercalate ps ++ " _ h " ++ outArg ++ " rfl"))
  | none => header ++ Format.nest 2 (Format.line ++ "by run_sound")

/-- The axiom audit of a theorem. -/
def audit (name : String) : Format := Format.text ("#audit_axioms " ++ name)

/-- The determinism theorem `R.det` of a relation:
`R ins outs → R ins outs' → outs = outs'`, by `det`. -/
def detTheorem (externs : Bool) (m : Member) : Format :=
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
  let name := m.localName.replace ".run" "" ++ ".det"
  Format.group (Format.nest 4 (Format.text ("theorem " ++ name) ++
    ext ++ ins ++ obs ++ " :" ++ Format.line ++ stmt ++ " :=")) ++
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
