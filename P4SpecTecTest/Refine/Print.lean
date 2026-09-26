import NanoP4Spec.«2.0-domain»
import P4SpecTec.Refine.Print

/-!
Nano printing needs the actual empty hint environment, not arbitrary policy
assumptions. Equal canonical inputs can select different hinted policies when
their constructor provenance differs. These tests retain the generated notes
and exercise the reusable unhinted congruence theorem instead of erasing them.
The quotation executable checks emptiness against the decoded Nano export.
-/

namespace P4SpecTecTest.NanoPrint

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Domain

def sourceIdentifier (s : ByteText) : Lang.Il.value :=
  NanoP4Spec.identifier.toValue (._ID s)

def generatedName (s : ByteText) : NanoP4Spec.nonTypeName := ._ID s

theorem identifierRelName (s : ByteText) : Rel (sourceIdentifier s) (generatedName s) := rfl

/-- info: 'P4SpecTecTest.NanoPrint.identifierRelName' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms identifierRelName

theorem sourceNote (s : ByteText) :
    (sourceIdentifier s).note.typ = Prelude.Value.varT "identifier" := rfl

/-- info: 'P4SpecTecTest.NanoPrint.sourceNote' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceNote

theorem generatedNote (s : ByteText) :
    (toValue (generatedName s)).note.typ = Prelude.Value.varT "nonTypeName" := rfl

/-- info: 'P4SpecTecTest.NanoPrint.generatedNote' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms generatedNote

theorem identifierNamePrint (s : ByteText) :
    P4.Unparse.printWithHints [] (sourceIdentifier s) =
      P4.Unparse.printWithHints [] (toValue (generatedName s)) :=
  printEqOfRel (identifierRelName s)

/-- info: 'P4SpecTecTest.NanoPrint.identifierNamePrint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms identifierNamePrint

def idMixop : Mixfix.mixop :=
  .Seq [.Atom (Prelude.Value.atom (.Tag "ID")), .Arg ()]

-- Synthetic policies, not the pinned Nano policy table. The same canonical
-- value and mixop can choose different policies in different type families.
def incompatibleHints : P4.Unparse.HEnv :=
  [("identifier", idMixop, .TextH "source"),
   ("nonTypeName", idMixop, .TextH "generated")]

def hdr : ByteText := ByteText.ofString "hdr"

#guard (P4.Unparse.printWithHints incompatibleHints (sourceIdentifier hdr)).toOption ==
  some "source"
#guard (P4.Unparse.printWithHints incompatibleHints (toValue (generatedName hdr))).toOption ==
  some "generated"
#guard (P4.Unparse.printWithHints [] (sourceIdentifier hdr)).toOption == some "hdr"
#guard (NanoP4Spec.«$print_» (generatedName hdr)).bind Except.toOption == some hdr
#guard (NanoP4Spec.«$id» (generatedName hdr)).bind Except.toOption == some hdr

-- Canon changes function identity and the extern JSON payload. Neither can
-- become printable: both must remain errors, including under a list wrapper.
def functionValue : Lang.Il.value :=
  ⟨.FuncV (Util.Source.mkPhrase "differentFunction"), dummy, Util.Source.no_region⟩

def externValue : Lang.Il.value :=
  Runtime.Value.Make.extern (Prelude.Value.varT "objectState")
    (Lean.Json.mkObj [("packet", .num 7)])

#guard !(P4.Unparse.printWithHints [] functionValue).isOk
#guard !(P4.Unparse.printWithHints [] (canon functionValue)).isOk
#guard !(P4.Unparse.printWithHints [] externValue).isOk
#guard !(P4.Unparse.printWithHints [] (canon externValue)).isOk
#guard !(P4.Unparse.printWithHints []
  ⟨.ListV [externValue], dummy, Util.Source.no_region⟩).isOk

end P4SpecTecTest.NanoPrint
