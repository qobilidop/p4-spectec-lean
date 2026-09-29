import P4SpecTec.Codegen.Certificates.Reverse

/-!
Abstract extern contracts (design section 9.2). The reference calls the configured callback
`cfg.extern.eval_extern_rel`; the generated code calls a method of the `Externs` class.
`externsContract` states their two-way correspondence on related inputs, for every extern
relation, without assuming a concrete implementation. Invocation certificates follow from it,
and callers whose closure reaches an extern state the contract as a hypothesis; the concrete
target discharges it separately (N4). Extern functions have no contract here yet.
-/

namespace P4SpecTec.Codegen.ExternCertificates

open Std (Format)
open P4SpecTec.Domain
open P4SpecTec.Codegen.Types P4SpecTec.Codegen.Exp P4SpecTec.Codegen.Funcs
open P4SpecTec.Codegen.Props

/-- The certificate member of an extern relation. Its generated computation is the method
of the `Externs` class, so every statement quantifies that instance and the contract. -/
def member (env : Env) (d : Lang.Al.def) : Option Member :=
  match d.it with
  | .ExternRelD i nottyp inputs _ =>
    let args := (Mixfix.args nottyp.it).map (·.it)
    let (ins, outs) := splitArgs (inputs.map (·.toNat)) args
    let name := "Externs." ++ Names.relName i.it
    some { id := i.it, isRel := true, defName := env.q name, localName := name
           params := ins.map (typTerm env []), ret := typTerm.prod (outs.map (typTerm env []))
           nOuts := outs.length, externs := true }
  | _ => none

/-- The reference callback on the inputs `v0, v1, ...`. -/
def callback (m : Member) : String :=
  let vs := (List.range m.params.length).map fun i => s!"v{i}"
  s!"cfg.extern.eval_extern_rel {m.id.quote} [" ++ ", ".intercalate vs ++ "]"

/-- One extern relation's clause of the contract: both directions on related inputs. -/
def clause (m : Member) : Format :=
  let n := m.params.length
  let vs := (List.range n).map fun i => s!"v{i}"
  let values := if n == 0 then Format.nil
    else Format.text ("(" ++ " ".intercalate vs ++ " : Lang.Il.value)")
  let rels := Format.join ((List.range n).map fun i =>
    Format.line ++ Format.text s!"Rel v{i} p{i} →")
  Format.paren (Format.group (Format.nest 2 (Format.text "∀ " ++ values ++
    paramBinders m.params ++ "," ++ rels ++ Format.line ++
    Format.group (Format.nest 2 (Format.text "Refines " ++ Validate.resultRel m ++ Format.line ++
      Format.paren (Format.text (callback m)) ++ Format.line ++ Validate.generated m)) ++
    " ∧" ++ Format.line ++
    Format.group (Format.nest 2 (Format.text "Realizes " ++ Validate.resultRel m ++
      Format.line ++ Format.paren (Format.text ("fun _ => " ++ callback m)) ++ Format.line ++
      Validate.generated m)))))

/-- The contract as a definition over the configured callbacks and the generated instance. -/
def contract (members : List Member) : Format :=
  let body := if members.isEmpty then Format.text "True"
    else Format.joinSep (members.map clause) (Format.text " ∧" ++ Format.line)
  Format.text ("/-- The abstract extern contract: on related inputs, every reference " ++
    "callback outcome has a\nrelated generated extern outcome and conversely, for every " ++
    "extern relation. Certificates\nof callers assume it; the concrete target discharges " ++
    "it separately. -/") ++ Term.hardLine ++
  Format.group (Format.nest 4 (Format.text
    "def externsContract [Externs] (cfg : Interp_al.Interp.Config) : Prop :=" ++
    Format.line ++ body))

/-- The projection of the `k`-th of `n` contract clauses. -/
def projection (k n : Nat) : String :=
  String.join ((List.range k).map fun _ => ".2") ++ (if k < n - 1 then ".1" else "")

/-- The arguments passed to a contract clause. -/
def clauseArguments (m : Member) : String :=
  let n := m.params.length
  " ".intercalate ((List.range n).map (s!"v{·}") ++ paramNames n ++ (List.range n).map (s!"h{·}"))

/-- The invocation certificates of each extern relation, derived from the contract. -/
def theorems (lib : String) (members : List Member) : List Format := Id.run do
  let n := members.length
  let mut out := [contract members]
  for (m, k) in members.zipIdx do
    let owner := m.localName
    let clauseTerm := s!"(hextern{projection k n} {clauseArguments m})"
    let holds := s!"have hrel : Holds ctx.global {lib}.{Names.relName m.id}.al := by " ++
      "holds_from_spec"
    out := out ++ [
      Format.group (Format.nest 4 (Format.text ("theorem " ++ owner ++ ".refines") ++
        Format.line ++ "(fuel : Nat)" ++ Format.line ++ Validate.binders lib m ++ " :" ++
        Format.line ++ Validate.conclusion m ++ " := by")) ++
        Format.nest 2 (Format.line ++ Format.text holds ++ Format.line ++
          Format.text s!"exact externRelRefines hguard internal hrel {clauseTerm}.1 fuel"),
      Validate.audit (m.defName ++ ".refines"),
      Format.group (Format.nest 4 (Format.text ("theorem " ++ owner ++ ".realizes") ++
        Format.line ++ Validate.binders lib m ++ " :" ++
        Format.line ++ Reverse.conclusion m ++ " := by")) ++
        Format.nest 2 (Format.line ++ Format.text holds ++ Format.line ++
          Format.text s!"exact externRelRealizes hguard internal hrel {clauseTerm}.2"),
      Validate.audit (m.defName ++ ".realizes"),
      Format.group (Format.nest 4 (Format.text ("theorem " ++ owner ++ ".invocations") ++
        Format.line ++ Validate.binders lib m ++ " :" ++ Format.line ++
        Format.text "(∀ fuel : Nat, " ++ Validate.conclusion m ++ ") ∧" ++ Format.line ++
        Reverse.conclusion m ++ " :=")) ++
        Format.nest 2 (Format.line ++ Format.fill (Format.nest 2 (Format.joinSep
          ((["⟨fun fuel =>", owner ++ ".refines", "fuel"] ++ argumentWords m).map Format.text ++
            [Format.text ",", Format.text (owner ++ ".realizes")] ++
            (argumentWords m).map Format.text ++ [Format.text "⟩"]) Format.line))),
      Validate.audit (m.defName ++ ".invocations")]
  return out
where
  /-- The binder names of an invocation certificate, in order after the fuel. -/
  argumentWords (m : Member) : List String :=
    let n := m.params.length
    Validate.configArguments m ++ (List.range n).map (s!"v{·}") ++
      paramNames n ++ (List.range n).map (s!"h{·}")

/-- The closed type of an extern relation's combined invocation certificate. -/
def invocationType (lib : String) (m : Member) : Format :=
  Format.group (Format.nest 4 (Format.text "∀" ++ Format.line ++ Validate.binders lib m ++ "," ++
    Format.line ++ Format.text "(∀ fuel : Nat, " ++ Validate.conclusion m ++ ") ∧" ++
    Format.line ++ Reverse.conclusion m))

end P4SpecTec.Codegen.ExternCertificates
