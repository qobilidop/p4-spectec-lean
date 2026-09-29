import P4SpecTec.Codegen.Certificates.SourceBuiltin
import P4SpecTec.Refine.Quote

/-! Exact source-shape recognition and successful-output preservation for natural repetition. -/

namespace P4SpecTec.Codegen.SourcePolymorphicRepeat
open P4SpecTec.Lang.Il P4SpecTec.Refine

private def variable? (e : exp) : Option String := do
  let .VarE name := e.it | none
  some name.it

private def inputNames? (c : clause) : Option (String × String) := do
  let ([a, b], _, _) := c.it | none
  let .ExpA a := a.it | none
  let .ExpA b := b.it | none
  let x ← variable? a
  let n ← variable? b
  guard (x != n)
  some (x, n)

/-- Match the complete two-clause natural repetition body, up to its binder names and regions.
Reification compares every expression, type note, premise and recursive callee using the same
region-erased syntax as the source quotation. Arbitrary functions of the same signature reject. -/
def recognizes (d : Lang.Al.def) : Bool := (do
  let .FuncDecD name [parameter] inputs result [base, step] none _ := d.it | none
  let xType := Q.varT parameter.it []
  let natType := Lang.Il.typ'.NumT .NatT
  let intType := Lang.Il.typ'.NumT .IntT
  let listType := Lang.Il.typ'.IterT (Q.t xType) .List
  let [.mk (.ExpP a) _ _, .mk (.ExpP b) _ _] := inputs | none
  guard (Types.typEq a.it xType && Types.typEq b.it natType &&
    Types.typEq result.it listType)
  let (x0, n0) ← inputNames? base
  let (x1, n1) ← inputNames? step
  let (_, _, [_, binding, _, cast]) := step.it | none
  let .LetPr intermediate _ := binding.it | none
  let .LetPr decreased _ := cast.it | none
  let i ← variable? intermediate
  let n' ← variable? decreased
  guard ([x1, n1, i, n'].eraseDups.length == 4)
  let v (name : String) (type : typ') := Q.e (.VarE (Q.i name)) type
  let num (n : Nat) := Q.e (.NumE (.Nat n)) natType
  let arg (e : exp) := Q.ar (.ExpA e)
  let baseExpected := Q.cl [arg (v x0 xType), arg (v n0 natType)]
    (Q.e (.ListE []) listType)
    [Q.pr (.IfPr (Q.e (.CmpE .EqOp .BoolT (v n0 natType) (num 0)) .BoolT))]
  let stepExpected := Q.cl [arg (v x1 xType), arg (v n1 natType)]
    (Q.e (.CatE (Q.e (.ListE [v x1 xType]) listType)
      (Q.e (.CallE name [Q.t xType] [arg (v x1 xType), arg (v n' natType)])
        listType)) listType)
    [Q.pr (.IfPr (Q.e (.CmpE .NeOp .BoolT (v n1 natType) (num 0)) .BoolT)),
     Q.pr (.LetPr (v i intType)
       (Q.e (.BinE .SubOp .IntT (v n1 natType) (num 1)) intType)),
     Q.pr (.IfPr (Q.e (.SubE (v i intType) (Q.t natType)
       (.RecurseSC (Q.t natType))) .BoolT)),
     Q.pr (.LetPr (v n' natType)
       (Q.e (.DownCastE (Q.t natType) (v i intType)) natType))]
  guard ((Reify.clause base).fmt.pretty == (Reify.clause baseExpected).fmt.pretty)
  guard ((Reify.clause step).fmt.pretty == (Reify.clause stepExpected).fmt.pretty)
  some true).getD false

/-- Prove preservation of arbitrary admitted elements by induction on the actual natural count.
Unfold once per induction case; recursive simplifier unfolding would loop. -/
def proof (functionName : String) : String :=
  "induction p1 generalizing result with\n" ++
  "| zero =>\n" ++
  s!"  rw [{functionName}] at run\n" ++
  "  simp [Eval.check] at run\n" ++
  "  subst result\n" ++
  "  simp\n" ++
  "| succ n ih =>\n" ++
  s!"  rw [{functionName}] at run\n" ++
  "  simp [Eval.check, Num.natSub, Num.toNat?] at run\n" ++
  "  obtain ⟨outcome, recRun, mapped⟩ := run\n" ++
  "  cases outcome with\n" ++
  "  | error e => cases mapped\n" ++
  "  | ok tail =>\n" ++
  "    cases Except.ok.inj mapped\n" ++
  "    intro y member\n" ++
  "    rcases List.mem_cons.mp member with rfl | member\n" ++
  "    · exact hp0\n" ++
  "    · exact ih tail recRun y member"

end P4SpecTec.Codegen.SourcePolymorphicRepeat
