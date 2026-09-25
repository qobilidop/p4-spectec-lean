import P4SpecTec.Lang.Il.Json
import P4SpecTec.Lang.Al.Ast

/-!
Not a mirror: this module is ours, placed beside the module whose values it
decodes.

Not a mirror: this module is our own, placed beside the module it decodes.

JSON decoders for the AL, following the `[@@deriving yojson]` encoding of
`p4spec/lib/lang/al/ast.ml`. Everything but rules, table rows and
definitions is decoded by `P4SpecTec.Lang.Il.Json`.
-/

namespace P4SpecTec.Lang.Al.Json

open Lean (Json)
open P4SpecTec.Util.Yojson
open P4SpecTec.Lang.Il.Json (id typ nottyp exp prem arg param tparam deftyp hint inputs clause)

/-- Decode `rulematch`. -/
def rulematch : D rulematch := triple (list exp) (list exp) (list prem)

/-- Decode `rulepath`. -/
def rulepath : D rulepath := triple id (list prem) (list exp)

/-- Decode `rulegroup`. -/
def rulegroup : D rulegroup := phrase (triple id rulematch (list rulepath))

/-- Decode `elsegroup`. -/
def elsegroup : D elsegroup := phrase (triple id rulematch rulepath)

/-- Decode `tablerow`. -/
def tablerow : D tablerow := phrase (quad (list exp) (list arg) exp (list prem))

/-- Decode `def'`. -/
def def' : D def' := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "ExternTypD", #[i, hs] => do pure (.ExternTypD (← id i) (← list hint hs))
  | "TypD", #[i, tps, dt, hs] => do
    pure (.TypD (← id i) (← list tparam tps) (← deftyp dt) (← list hint hs))
  | "VarD", #[i, t, hs] => do pure (.VarD (← id i) (← typ t) (← list hint hs))
  | "ExternRelD", #[i, n, ins, hs] => do
    pure (.ExternRelD (← id i) (← nottyp n) (← inputs ins) (← list hint hs))
  | "RelD", #[i, n, ins, rgs, eg, hs] => do
    pure (.RelD (← id i) (← nottyp n) (← inputs ins) (← list rulegroup rgs)
      (← opt elsegroup eg) (← list hint hs))
  | "ExternDecD", #[i, tps, ps, t, hs] => do
    pure (.ExternDecD (← id i) (← list tparam tps) (← list param ps) (← typ t) (← list hint hs))
  | "BuiltinDecD", #[i, tps, ps, t, hs] => do
    pure (.BuiltinDecD (← id i) (← list tparam tps) (← list param ps) (← typ t) (← list hint hs))
  | "TableDecD", #[i, ps, t, rows, hs] => do
    pure (.TableDecD (← id i) (← list param ps) (← typ t) (← list tablerow rows) (← list hint hs))
  | "FuncDecD", #[i, tps, ps, t, cs, ec, hs] => do
    pure (.FuncDecD (← id i) (← list tparam tps) (← list param ps) (← typ t) (← list clause cs)
      (← opt clause ec) (← list hint hs))
  | _, _ => fail "expected AL def'" j

/-- Decode `def`. -/
def «def» : D «def» := phrase def'

/-- Decode `spec`. -/
def spec : D spec := list «def»

/-- Read and decode a spec export from a file. -/
def readSpec (path : System.FilePath) : IO Lang.Al.spec := do
  let json ← Util.Yojson.readFile path
  IO.ofExcept (spec json)

end P4SpecTec.Lang.Al.Json
