import P4SpecTec.Lang.Il.Ast

/-!
The AL (algorithmic language) abstract syntax. Mirrors
`p4spec/lib/lang/al/ast.ml`: every type is the IL's, except that rule
groups are split into a shared match and rule paths, table rows carry
premises, and definitions and specs are rebuilt over those. The compiler
consumes AL, the output of upstream's `algo` pass (binding analysis and
guard insertion), which is what the AL interpreter runs.
-/

namespace P4SpecTec.Lang.Al

open P4SpecTec.Util.Source
open P4SpecTec.Lang.Il

/- Rules -/

/-- Mirrors `rulematch = exp list * exp list * prem list`: the signature
expressions, the input expressions and the matching premises. -/
abbrev rulematch := List exp × List exp × List prem

/-- Mirrors `rulepath = id * prem list * exp list`: the rule, its
premises and its output expressions. -/
abbrev rulepath := id × List prem × List exp

/-- Mirrors `rulegroup'`. -/
abbrev rulegroup' := id × rulematch × List rulepath

/-- Mirrors `rulegroup`. -/
abbrev rulegroup := phrase rulegroup'

/-- Mirrors `elsegroup'`. -/
abbrev elsegroup' := id × rulematch × rulepath

/-- Mirrors `elsegroup`. -/
abbrev elsegroup := phrase elsegroup'

/- Table rows -/

/-- Mirrors `tablerow' = exp list * arg list * exp * prem list`. -/
abbrev tablerow' := List exp × List arg × exp × List prem

/-- Mirrors `tablerow`. -/
abbrev tablerow := phrase tablerow'

/- Definitions -/

/-- Mirrors `def'`. -/
inductive def' where
  /-- `extern` `syntax` id hint* -/
  | ExternTypD (id : id) (hints : List hint)
  /-- `syntax` id `<` list(tparam, `,`) `>` `=` deftyp hint* -/
  | TypD (id : id) (tparams : List tparam) (deftyp : deftyp) (hints : List hint)
  /-- `var` id `:` typ hint* -/
  | VarD (id : id) (typ : typ) (hints : List hint)
  /-- `extern` `relation` id `:` nottyp `hint(input` `%`int* `)` hint* -/
  | ExternRelD (id : id) (nottyp : nottyp) (inputs : Hints.Input.t) (hints : List hint)
  /-- `relation` id `:` nottyp `hint(input` `%`int* `)` rulegroup* hint* -/
  | RelD (id : id) (nottyp : nottyp) (inputs : Hints.Input.t) (rulegroups : List rulegroup)
      (elsegroup : Option elsegroup) (hints : List hint)
  /-- `extern` `dec` id `<` list(tparam, `,`) `>` list(param, `,`) `:` typ hint* -/
  | ExternDecD (id : id) (tparams : List tparam) (params : List param) (typ : typ)
      (hints : List hint)
  /-- `builtin` `dec` id `<` list(tparam, `,`) `>` list(param, `,`) `:` typ hint* -/
  | BuiltinDecD (id : id) (tparams : List tparam) (params : List param) (typ : typ)
      (hints : List hint)
  /-- `table` `dec` id list(param, `,`) `:` typ hint* -/
  | TableDecD (id : id) (params : List param) (typ : typ) (rows : List tablerow)
      (hints : List hint)
  /-- `dec` id `<` list(tparam, `,`) `>` list(param, `,`) `:` typ clause* hint* -/
  | FuncDecD (id : id) (tparams : List tparam) (params : List param) (typ : typ)
      (clauses : List clause) (elseclause : Option elseclause) (hints : List hint)

/-- Mirrors `def`. -/
abbrev «def» := phrase def'

/- Spec -/

/-- Mirrors `spec`. -/
abbrev spec := List «def»

/-- The identifier a definition declares. -/
def def'.id : def' → id
  | .ExternTypD id _ | .TypD id .. | .VarD id .. | .ExternRelD id .. | .RelD id ..
  | .ExternDecD id .. | .BuiltinDecD id .. | .TableDecD id .. | .FuncDecD id .. => id

end P4SpecTec.Lang.Al
