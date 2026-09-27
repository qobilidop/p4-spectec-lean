import P4SpecTec.Codegen.Certificates.Forward

/-!
Operation-specific builtin certificates over represented inputs. Actual source
signatures select checked family contracts; source-domain coverage and legal
polymorphic instances remain independent obligations.
-/

namespace P4SpecTec.Codegen.BuiltinCertificates

open Std (Format)
open P4SpecTec.Lang.Il P4SpecTec.Codegen.Types P4SpecTec.Codegen.Exp

/-- The two checked directions of a represented-input builtin contract. -/
inductive Direction where
  /-- Every terminating reference outcome has a related generated outcome. -/
  | forward
  /-- Every terminating generated outcome has an eventual reference witness. -/
  | reverse
  deriving BEq

/-- A source signature paired with its operation-specific proof family. -/
structure Signature where
  /-- Number of declared type parameters. -/
  typeArity : Nat
  /-- Parameter shapes, with type parameters numbered in declaration order. -/
  inputs : List String
  /-- Result shape. -/
  output : String

/-- The supported pinned operation signatures, independent of generated wrapper bodies. -/
def signature : String → Option Signature
  | "print_" => some ⟨1, ["$0"], "text"⟩
  | "strip_all_whitespace" => some ⟨0, ["text"], "text"⟩
  | "rev_" => some ⟨1, ["list($0)"], "list($0)"⟩
  | "distinct_" => some ⟨1, ["list($0)"], "bool"⟩
  | "assoc_" => some ⟨2, ["$0", "list(tuple($0,$1))"], "option($1)"⟩
  | "intersect_set" | "union_set" | "diff_set" =>
      some ⟨1, ["set($0)", "set($0)"], "set($0)"⟩
  | "unions_set" => some ⟨1, ["list(set($0))"], "set($0)"⟩
  | "sub_set" | "eq_set" => some ⟨1, ["set($0)", "set($0)"], "bool"⟩
  | "find_map" => some ⟨2, ["map($0,$1)", "$0"], "option($1)"⟩
  | "find_maps" => some ⟨2, ["list(map($0,$1))", "$0"], "option($1)"⟩
  | "add_map" | "update_map" => some ⟨2, ["map($0,$1)", "$0", "$1"], "map($0,$1)"⟩
  | "bitstr_to_int" | "int_to_bitstr" | "band" | "bxor" | "bor" =>
      some ⟨0, ["int", "int"], "int"⟩
  | "pow2" => some ⟨0, ["nat"], "int"⟩
  | "bneg" => some ⟨0, ["int"], "int"⟩
  | "bits_to_int_unsigned" | "bits_to_int_signed" => some ⟨0, ["bits"], "int"⟩
  | "int_to_bits_unsigned" | "int_to_bits_signed" => some ⟨0, ["nat", "int"], "bits"⟩
  | _ => none

/-- Metadata-free signature shapes preserve aliases used by the actual wrapper adaptation. -/
partial def shape (parameters : List String) : typ' → String
  | .TextT => "text"
  | .BoolT => "bool"
  | .NumT .NatT => "nat"
  | .NumT .IntT => "int"
  | .VarT name args =>
      let head := match parameters.idxOf? name.it with
        | some index => s!"${index}"
        | none => name.it
      if args.isEmpty then head
      else head ++ "(" ++ ",".intercalate (args.map fun t => shape parameters t.it) ++ ")"
  | .IterT t .List => "list(" ++ shape parameters t.it ++ ")"
  | .IterT t .Opt => "option(" ++ shape parameters t.it ++ ")"
  | .TupleT ts => "tuple(" ++ ",".intercalate (ts.map fun t => shape parameters t.it) ++ ")"
  | _ => "unsupported"

/-- Printing needs an extra environment contract which callers must explicitly preserve. -/
def requiresPrintHints (d : Lang.Al.def) : Bool :=
  match d.it with
  | .BuiltinDecD name .. => name.it == "print_"
  | _ => false

/-- Reject unknown operations, changed signatures, callbacks and stateful wrappers. -/
def checkSupport (env : Env) (d : Lang.Al.def) : Except String Unit := do
  unless env.mode == .pure do throw "stateful builtin certificates are not implemented"
  let .BuiltinDecD name tps ps ret _ := d.it | throw "not a builtin declaration"
  let some expected := signature name.it | throw s!"no builtin contract for {name.it}"
  let names := tps.map (·.it)
  unless names.length == expected.typeArity && names.eraseDups == names do
    throw s!"builtin contract type parameters differ: {name.it}"
  let inputs ← ps.mapM fun p => match p.it with
    | .ExpP t => pure (shape names t.it)
    | _ => throw s!"builtin contract callback is unsupported: {name.it}"
  unless inputs == expected.inputs && shape names ret.it == expected.output do
    throw s!"builtin contract signature differs: {name.it}"
  if name.it == "print_" then
    let hints ← P4.Unparse.hints_of_spec_al env.defs
    unless hints.isEmpty do throw "builtin print contract requires an empty generated hint table"
  let mapOperation := name.it.endsWith "_map" || name.it == "find_maps"
  if name.it.endsWith "_set" || mapOperation then
    let some info := env.types.get? "set" | throw "builtin contract needs set carrier"
    let some (.VariantT [c]) := info.deftyp | throw "builtin contract set shape differs"
    let .Brack left (.Arg element) right := c.nottyp.it
      | throw "builtin contract set notation differs"
    unless info.tparams.length == 1 && left.it == .LBrace && right.it == .RBrace &&
        shape info.tparams element.it == "list($0)" do
      throw "builtin contract set payload differs"
  if mapOperation then
    let some info := env.types.get? "pair" | throw "builtin contract needs pair carrier"
    let some (.VariantT [c]) := info.deftyp | throw "builtin contract pair shape differs"
    let .Seq [.Arg key, .Atom colon, .Arg val] := c.nottyp.it
      | throw "builtin contract pair notation differs"
    unless info.tparams.length == 2 && colon.it == .Operator ":" &&
        shape info.tparams key.it == "$0" && shape info.tparams val.it == "$1" do
      throw "builtin contract pair payload differs"
    let some info := env.types.get? "map" | throw "builtin contract needs map alias"
    let some (.PlainT alias) := info.deftyp | throw "builtin contract map alias differs"
    unless info.tparams.length == 2 && shape info.tparams alias.it == "set(pair($0,$1))" do
      throw "builtin contract map payload differs"
  if expected.inputs.contains "bits" || expected.output == "bits" then
    let some info := env.types.get? "bits" | throw "builtin contract needs bits alias"
    let some (.PlainT alias) := info.deftyp | throw "builtin contract bits alias differs"
    let .IterT element .List := alias.it | throw "builtin contract bits payload differs"
    unless info.tparams.isEmpty && shape [] (env.resolve element.it) == "bool" do
      throw "builtin contract bits element differs"

private def parts (d : Lang.Al.def) : List String × List typ' :=
  match d.it with
  | .BuiltinDecD _ tps ps _ _ => (tps.map (·.it), Funcs.paramTypes (ps.map (·.it)))
  | _ => ([], [])

private def rawTypes (d : Lang.Al.def) : List String :=
  (List.range (parts d).1.length).map fun i => s!"t{i}"

private def rawValues (d : Lang.Al.def) : List String :=
  (List.range (parts d).2.length).map fun i => s!"v{i}"

private def listText (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

private def wrapper (env : Env) (d : Lang.Al.def) : String :=
  "(" ++ env.q (Names.funcName d.it.id.it) ++ " " ++
    " ".intercalate (Funcs.paramNames (parts d).2.length) ++ ")"

private def binders (env : Env) (d : Lang.Al.def) (invocation : Bool) : Format :=
  let (tps, ps) := parts d
  let typed := Funcs.binders env tps ps false
  let types := if tps.isEmpty then "" else
    " (" ++ " ".intercalate (rawTypes d) ++ " : Lang.Il.typ)"
  let values := if ps.isEmpty then "" else
    " (" ++ " ".intercalate (rawValues d) ++ " : Lang.Il.value)"
  let rels := String.join ((List.range ps.length).map fun i => s!" (h{i} : Rel v{i} p{i})")
  let printHints := if d.it.id.it == "print_" then " (hhints : cfg.printHints = [])" else ""
  let context := if invocation then
    " (ctx : Interp_al.Ctx.t) (internal : Bool)" ++
    " (hguard : cfg.guard = false) (hfenv : ctx.local.fenv = [])" ++
    s!" (hdecl : Holds ctx.global {env.q (Names.funcName d.it.id.it)}.al)"
    else ""
  typed ++ Format.line ++ Format.text
    (types ++ values ++ rels ++ " (cfg : Interp_al.Interp.Config)" ++ printHints ++ context)

private def invocation (d : Lang.Al.def) (fuel : String) : String :=
  s!"Interp_al.Interp.invoke_func {fuel} cfg internal ctx (Q.i {d.it.id.it.quote}) " ++
    listText (rawTypes d) ++ " " ++ listText (rawValues d)

private def conclusion (env : Env) (d : Lang.Al.def) (direction : Direction) : String :=
  let generated := "(ExceptT.mk " ++ wrapper env d ++ ")"
  match direction with
  | .forward => "Refines Rel (" ++ invocation d "fuel" ++ ") " ++ generated
  | .reverse => "Realizes Rel (fun fuel => " ++ invocation d "fuel" ++ ") " ++ generated

/-- The exact type shared by emission and compiled theorem checking. -/
def theoremType (env : Env) (d : Lang.Al.def) (direction : Direction) : Except String Format := do
  checkSupport env d
  let fuel := if direction == .forward then " (fuel : Nat)" else ""
  pure (Format.group (Format.nest 2 (Format.text ("∀" ++ fuel) ++
    binders env d true ++ "," ++ Format.line ++ Format.text (conclusion env d direction))))

private def canonicalType (env : Env) (d : Lang.Al.def) : String :=
  "(Interp_al.Effects.builtinEval cfg.printHints " ++ d.it.id.it.quote ++ " " ++
    listText (rawTypes d) ++ " " ++ listText (rawValues d) ++ ").run.map (Except.map canon) =
" ++
    "  " ++ wrapper env d ++ ".map (Except.map (fun x => canon (toValue x)))"

/-- The qualified public operation contract name. -/
def dispatchName (env : Env) (d : Lang.Al.def) : String :=
  env.q (Names.funcName d.it.id.it) ++ ".dispatch"

/-- The qualified invocation certificate name in the requested direction. -/
def theoremName (env : Env) (d : Lang.Al.def) (direction : Direction) : String :=
  env.q (Names.funcName d.it.id.it) ++
    (if direction == .forward then ".refines" else ".realizes")

/-- The exact closed operation-specific dispatch contract type. -/
def dispatchType (env : Env) (d : Lang.Al.def) : Except String Format := do
  checkSupport env d
  pure (Format.group (Format.nest 2 (Format.text "∀" ++ binders env d false ++ "," ++
    Format.line ++ Format.text (canonicalType env d))))

private def numericProof (id : String) : Option String :=
  match id with
  | "bitstr_to_int" => some "bitstrToIntRun h0 h1"
  | "int_to_bitstr" => some "intToBitstrRun h0 h1"
  | "pow2" => some "pow2Run h0"
  | "bneg" => some "bnegRun h0"
  | "band" => some "bandRun h0 h1"
  | "bxor" => some "bxorRun h0 h1"
  | "bor" => some "borRun h0 h1"
  | "bits_to_int_unsigned" => some "bitsToIntUnsignedRun h0"
  | "bits_to_int_signed" => some "bitsToIntSignedRun h0"
  | "int_to_bits_unsigned" => some "intToBitsUnsignedRun h0 h1"
  | "int_to_bits_signed" => some "intToBitsSignedRun h0 h1"
  | _ => none

private def primitiveProof (_env : Env) (d : Lang.Al.def) : Option String := Id.run do
  let id := d.it.id.it
  if let some proof := numericProof id then
    if id.startsWith "int_to_bits_" then
      return some s!"exact Refine.Builtin.Numeric.{proof} cfg.printHints"
    else return some (s!"rw [Refine.Builtin.Numeric.{proof} cfg.printHints]\n" ++
      "simp only [Option.map_map, Function.comp_def]\n" ++
      "congr 1\nfunext result\ncases result <;> rfl")
  match id with
  | "print_" => some ("rw [hhints, Refine.printBuiltinRunOfRel h0 [t0]]\n" ++
      "simp only [Option.map_map, Function.comp_def]\n" ++
      "congr 1\nfunext result\ncases result <;> rfl")
  | "strip_all_whitespace" =>
      some "rw [Refine.Builtin.Text.stripWhitespaceRunOfRel h0 cfg.printHints]\nrfl"
  | "distinct_" =>
      some "rw [Refine.Builtin.List.distinctRunOfRel h0 cfg.printHints [t0]]\nrfl"
  | "rev_" | "assoc_" =>
      let call := if id == "rev_" then "reverseRunOfRel h0 cfg.printHints t0"
        else "assocRunOfRel h0 h1 cfg.printHints t0 t1"
      some (s!"obtain ⟨out, run, rel⟩ := Refine.Builtin.List.{call}\n" ++
        "rw [run]\n" ++
        "change some (Except.ok (ε := Fail) (canon out)) = " ++
        "some (Except.ok (ε := Fail) (canon (toValue _)))\n" ++
        "exact congrArg (fun v => some (Except.ok (ε := Fail) v)) rel")
  | _ => none

private def successProof : String :=
  "rw [run]\n" ++
  "change some (Except.ok (ε := Fail) (canon out)) = " ++
  "some (Except.ok (ε := Fail) (canon (toValue _)))\n" ++
  "exact congrArg (fun v => some (Except.ok (ε := Fail) v)) rel"

private def setProof (env : Env) (d : Lang.Al.def) : Option String :=
  let id := d.it.id.it
  let ctor := Funcs.dotted ((Funcs.stdCtor env "set").getD "unsupported")
  let binary := "rcases p0 with ⟨xs⟩\nrcases p1 with ⟨ys⟩\n" ++
    "change Rel v0 (Refine.Builtin.Collection.bracketed (xs.map toValue)) at h0\n" ++
    "change Rel v1 (Refine.Builtin.Collection.bracketed (ys.map toValue)) at h1\n"
  match id with
  | "intersect_set" | "union_set" | "diff_set" =>
      let op := if id == "intersect_set" then "intersect" else
        if id == "union_set" then "union" else "diff"
      some (binary ++ s!"obtain ⟨out, run, rel⟩ := Refine.Builtin.Set.{op}RunOfRel " ++
        "h0 h1 cfg.printHints t0\n" ++ successProof)
  | "sub_set" | "eq_set" =>
      let op := if id == "sub_set" then "sub" else "eq"
      some (binary ++ s!"rw [Refine.Builtin.Set.{op}RunOfRel h0 h1 cfg.printHints [t0]]\nrfl")
  | "unions_set" => some (String.join [
      s!"let sets := p0.map fun | {ctor} xs => xs\n",
      "have image : Rel v0 (sets.map fun xs => ",
      "Refine.Builtin.Collection.bracketed (xs.map toValue)) := by\n",
      "  change canon v0 = _ at h0 ⊢\n  rw [h0]\n",
      "  apply congrArg (fun entries => ",
      "(⟨.ListV entries, dummy, Util.Source.no_region⟩ : Lang.Il.value))\n",
      "  simp only [canons_eq_map, List.map_map, sets]\n",
      "  apply List.map_congr_left\n  intro entry _\n  cases entry\n  rfl\n",
      "obtain ⟨out, run, rel⟩ := Refine.Builtin.Set.unionsRunOfRel image cfg.printHints t0\n",
      successProof])
  | _ => none

private def mapProof (env : Env) (d : Lang.Al.def) : Option String := do
  let id := d.it.id.it
  unless ["find_map", "find_maps", "add_map", "update_map"].contains id do none
  let setCtor ← Funcs.stdCtor env "set"
  let pairCtor ← Funcs.stdCtor env "pair"
  let names := (parts d).1.map Names.tparamName
  let key := names[0]!
  let val := names[1]!
  let pair := env.q (Names.typeName "pair")
  let colon := pairCtor
  let image := String.join [
    s!"have image (entries : List ({pair} {key} {val})) :\n",
    "    Rel (Refine.Builtin.Map.encode (entries.map\n",
    s!"      (fun | {colon} k v => (k, v)))) ({setCtor} entries) := by\n",
    "  apply congrArg (fun entries =>\n",
    "    (⟨.CaseV (.Brack (Value.atom .LBrace)\n",
    "      (.Arg ⟨.ListV entries, dummy, Util.Source.no_region⟩) (Value.atom .RBrace)),\n",
    "      dummy, Util.Source.no_region⟩ : Lang.Il.value))\n",
    "  simp only [canons_eq_map, List.map_map]\n",
    "  apply List.map_congr_left\n  intro entry _\n  cases entry\n  rfl\n"]
  let binary := "rcases p0 with ⟨entries⟩\n" ++
    "have encoded := h0.trans (image entries).symm\n"
  let call := if id == "find_map" then "find" else
    if id == "find_maps" then "findMaps" else if id == "add_map" then "add" else "update"
  if id == "find_maps" then
    return String.join [image,
      s!"let maps : List (List ({key} × {val})) := p0.map (fun s => match s with\n",
      s!"  | {Funcs.dotted setCtor} entries =>\n",
      s!"    entries.map fun | {colon} k v => (k, v))\n",
      "have encoded : Rel v0 (maps.map Refine.Builtin.Map.encode) := by\n",
      "  change canon v0 = _ at h0 ⊢\n  rw [h0]\n",
      "  apply congrArg (fun entries => ",
      "(⟨.ListV entries, dummy, Util.Source.no_region⟩ : Lang.Il.value))\n",
      "  simp only [canons_eq_map, List.map_map, maps]\n",
      "  apply List.map_congr_left\n  intro entry _\n",
      s!"  rcases entry with ⟨entries⟩\n  exact (image entries).symm\n",
      "obtain ⟨out, run, rel⟩ := Refine.Builtin.Map.findMapsRunOfRel\n",
      "  encoded h1 cfg.printHints t0 t1\n", successProof]
  if id == "find_map" then
    return image ++ binary ++
      "obtain ⟨out, run, rel⟩ := Refine.Builtin.Map.findRunOfRel\n" ++
      "  encoded h1 cfg.printHints t0 t1\n" ++ successProof
  return String.join [image, binary,
    s!"obtain ⟨out, run, rel⟩ := Refine.Builtin.Map.{call}RunOfRel\n",
    "  encoded h1 h2 cfg.printHints t0 t1\n",
    "have outputImage (xs : List (", key, " × ", val, ")) :\n",
    "    Rel (Refine.Builtin.Map.encode xs) (", setCtor,
    " (xs.map fun p => ", pairCtor, " p.1 p.2)) := by\n",
    "  apply congrArg (fun entries =>\n",
    "    (⟨.CaseV (.Brack (Value.atom .LBrace)\n",
    "      (.Arg ⟨.ListV entries, dummy, Util.Source.no_region⟩) (Value.atom .RBrace)),\n",
    "      dummy, Util.Source.no_region⟩ : Lang.Il.value))\n",
    "  simp only [canons_eq_map, List.map_map]\n",
    "  apply List.map_congr_left\n  intro entry _\n  rfl\n",
    "rw [run]\n",
    "change some (Except.ok (ε := Fail) (canon out)) = " ++
      "some (Except.ok (ε := Fail) (canon (toValue _)))\n",
    "simpa only [", env.q (Names.funcName id),
    ", List.map_map, Function.comp_def, Prod.eta, List.map_id'] using\n",
    "  congrArg (fun v => some (Except.ok (ε := Fail) v)) (rel.trans (outputImage _))"]

/-- Proof-support modules required by represented-input builtin certificates. -/
def supportImports (d : Lang.Al.def) : List String :=
  let id := d.it.id.it
  let family := if id == "print_" then "P4SpecTec.Refine.Print"
    else if id == "strip_all_whitespace" then "P4SpecTec.Refine.Builtin.Text"
    else if ["rev_", "distinct_", "assoc_"].contains id then "P4SpecTec.Refine.Builtin.List"
    else if id.endsWith "_set" then "P4SpecTec.Refine.Builtin.Set"
    else if id.endsWith "_map" || id == "find_maps" then "P4SpecTec.Refine.Builtin.Map"
    else "P4SpecTec.Refine.Builtin.Numeric"
  ["P4SpecTec.Tactic.Audit", "P4SpecTec.Refine.Builtin.Invoke", family]

/-- Emit checked represented-input certificates; unsupported declarations fail closed. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String Format := do
  checkSupport env d
  let some proof := primitiveProof env d <|> setProof env d <|> mapProof env d
    | throw s!"builtin proof not implemented: {d.it.id.it}"
  let localName := Names.funcName d.it.id.it
  let qualified := env.q localName
  let canonical := Format.group (Format.nest 2 (
    Format.text s!"theorem {localName}.dispatch" ++ binders env d false ++ " :" ++
    Format.line ++ Format.text (canonicalType env d) ++ " := by")) ++
    Format.nest 2 (Format.line ++ Format.text proof)
  let arguments := "cfg hguard ctx internal " ++ d.it.id.it.quote ++
    " _ _ _ " ++ listText (rawTypes d) ++ " " ++ listText (rawValues d) ++ " hfenv hdecl"
  let canonicalArgs := Funcs.paramNames (parts d).2.length ++ rawTypes d ++ rawValues d ++
    (List.range (parts d).2.length).map (fun i => s!"h{i}") ++ ["cfg"] ++
    (if d.it.id.it == "print_" then ["hhints"] else [])
  let call := "(" ++ qualified ++ ".dispatch " ++ " ".intercalate canonicalArgs ++ ")"
  let thms := [Direction.forward, .reverse].map fun direction =>
    let suffix := if direction == .forward then "refines" else "realizes"
    let fuel := if direction == .forward then " (fuel : Nat)" else ""
    let adapter := if direction == .forward then
      "refinesInvokeOfCanonicalRun fuel" else "realizesOfCanonicalRun"
    Format.group (Format.nest 2 (Format.text s!"theorem {localName}.{suffix}{fuel}" ++
      binders env d true ++ " :" ++ Format.line ++
      Format.text (conclusion env d direction) ++ " := by")) ++
      Format.nest 2 (Format.line ++ Format.text
        ("exact Refine.Builtin." ++ adapter ++ " " ++ arguments ++ " " ++ call)) ++
      Format.line ++ Format.line ++ Validate.audit (qualified ++ "." ++ suffix)
  let output := Format.joinSep (canonical :: Validate.audit (qualified ++ ".dispatch") :: thms)
    (Format.line ++ Format.line)
  pure (Format.text (boundedLines output.pretty))

end P4SpecTec.Codegen.BuiltinCertificates
