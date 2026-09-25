import Lean.Elab.Deriving.BEq
import P4SpecTec.Lang.Al.Json

/-!
An independent structural comparison for the quoted AL. The source is
decoded using the ordinary JSON decoder; Lean's derived equality visits
every AST constructor and field, independently of `Codegen.Reify` and the
`Q` smart constructors. Only source regions and hints are erased. In
particular expression/path type notes, type origins, input positions and
list order are retained. These equality instances are test-only and are
not part of any proof.
-/

namespace P4SpecTecTest.Quote

open P4SpecTec P4SpecTec.Util.Source P4SpecTec.Lang.Il

-- Erase only regions in phrases; preserve the payload and the type note.
local instance {α β γ : Type} [BEq α] [BEq β] : BEq (info α β γ) where
  beq a b := a.it == b.it && a.note == b.note

-- In the AL AST, List Json occurs only as hints, including variant-case
-- hints. Ignore the entire list, including its length.
local instance : BEq (List hint) where
  beq _ _ := true

deriving instance BEq for Domain.Mixfix.t, listpattern, optpattern, pattern
deriving instance BEq for typ', deftyp', typorigin', typcase, vnote, value', subcheck,
  exp', var, iterexp, iterprem, path', param', arg', prem'
deriving instance BEq for Lang.Al.def'

def sameDef (a b : Lang.Al.def) : Bool := a == b

-- VarD declarations are intentionally absent from the generated spec:
-- Ctx.init uses type, function and relation declarations, not metavariables.
def quotedDomain (spec : Lang.Al.spec) : Lang.Al.spec :=
  spec.filter fun d => match d.it with | .VarD .. => false | _ => true

def compareSpecs (source quoted : Lang.Al.spec) : Except String Nat := do
  let expected := quotedDomain source
  if expected.length != quoted.length then
    throw s!"quotation length: expected {expected.length}, got {quoted.length}"
  for (a, b) in expected.zip quoted do
    if !sameDef a b then
      throw s!"quotation differs at {a.it.id.it} ({string_of_region a.at}); got {b.it.id.it}"
  return expected.length

end P4SpecTecTest.Quote
