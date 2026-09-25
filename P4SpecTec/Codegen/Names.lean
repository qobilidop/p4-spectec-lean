import P4SpecTec.IL.Ast
import P4SpecTec.Codegen.Keywords

/-!
The naming rule: how every spec name becomes a Lean name. One documented,
invertible rule (design section 2.1), no renaming for taste.

- A spec identifier is kept verbatim: type `typeIR` is `typeIR`, variable
  `TC'` is `TC'`. Iterated variables keep their dimensions: `x*` is `«x*»`,
  `x?` is `«x?»`. A type parameter `X` is `τX`, since a variable of that
  type is conventionally named `X` too. Every reference to a generated
  type, constructor, function or relation is qualified with the library
  name for the same reason: variables are named after their types.
- A function `$f` keeps its `$`: `«$f»`. The spec's namespaces for syntax
  types, relations, functions and variables overlap (Nano-P4 has both a
  type `id` and a function `$id`); the `$` keeps them apart in Lean too.
- A relation `R` is the inductive `R`; its executable form is `R.run`.
- A variant case is named by its atoms, joined by `_`: `nat W int` is `W`,
  `` INT `< nat `> `` is `INT_langle_rangle`, `` `{ K* `} `` is
  `lbrace_rbrace`. Symbol atoms take the names in `atomName`; an operator
  atom spells each character by `charName`. A case with no atom is `mk`.
  A tag atom keeps its underscore: `_ID`.
- A struct field is its atom's name: `TYPE`.
- A name that is a Lean token, or is not a Lean identifier, is quoted with
  `«»`. The token list is `Keywords.lean`, generated from Lean itself.
- A spec file is the module of the same name: `3.2-bits.watsup` under the
  spec root is `NanoP4Spec/3.2-bits.lean`, module `NanoP4Spec.«3.2-bits»`;
  a file in a subdirectory keeps the directory as a component. Every
  component is quoted when it is not an identifier. The tree of generated
  files is the tree of spec files.
-/

namespace P4SpecTec.Codegen.Names

open P4SpecTec.Domain
open P4SpecTec.IL

/-- Whether a character may start a Lean identifier (`τ` prefixes type
parameters; Lean accepts Greek letters other than λ, Π and Σ). -/
def isIdFirst (c : Char) : Bool := c.isAlpha || c == '_' || c == 'τ'

/-- Whether a character may continue a Lean identifier. -/
def isIdRest (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'

/-- Whether a string is a plain Lean identifier component and not a token. -/
def isPlainIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isIdFirst c && cs.all isIdRest && !(keywords.contains s) && s != "_"

/-- Quote a name with `«»` unless it is a plain identifier. -/
def escape (s : String) : String := if isPlainIdent s then s else "«" ++ s ++ "»"

/-- The name of a symbol atom. -/
def atomName : Atom.t → String
  | .Keyword s => s
  | .Tag s => "_" ++ s
  | .Operator s => String.join (s.toList.map charName)
  | .Sub => "sub" | .Sup => "sup" | .Turnstile => "turnstile" | .Tilesturn => "tilesturn"
  | .Arrow => "arrow" | .ArrowSub => "arrowsub" | .DoubleArrowSub => "darrowsub"
  | .DoubleArrowLong => "darrowlong" | .SqArrow => "sqarrow" | .SqArrowStar => "sqarrowstar"
  | .Dot => "dot" | .Dot2 => "dot2" | .Dot3 => "dot3" | .Semicolon => "semi" | .Colon => "colon"
  | .ColonEq => "coloneq" | .Tilde2 => "tilde2" | .Backslash => "backslash"
  | .LAngle => "langle" | .RAngle => "rangle" | .LParen => "lparen" | .RParen => "rparen"
  | .LBrack => "lbrack" | .RBrack => "rbrack" | .LBrace => "lbrace" | .RBrace => "rbrace"
where
  /-- The name of a character of an operator atom. -/
  charName (c : Char) : String :=
    match c with
    | '!' => "bang" | '~' => "tilde" | '-' => "minus" | '+' => "plus" | '*' => "star"
    | '/' => "slash" | '%' => "percent" | '<' => "lt" | '>' => "gt" | '=' => "eq"
    | '&' => "amp" | '^' => "caret" | '|' => "bar" | '#' => "hash" | '@' => "at"
    | '.' => "dot" | ',' => "comma" | ':' => "colon" | ';' => "semi" | '?' => "qmark"
    | '$' => "dollar" | '(' => "lparen" | ')' => "rparen" | '[' => "lbrack" | ']' => "rbrack"
    | '{' => "lbrace" | '}' => "rbrace" | '\'' => "quote" | '"' => "dquote" | ' ' => "space"
    | '\\' => "backslash"
    | c => if c.isAlphanum || c == '_' then String.singleton c else s!"u{c.toNat}"

/-- The constructor name of a case, from its mixop. -/
def ctorName {α : Type} (m : Mixfix.t α) : String :=
  match (Mixfix.atoms m).map (fun a => atomName a.it) with
  | [] => "mk"
  | names => escape ("_".intercalate names)

/-- The Lean name of a spec type. -/
def typeName (id : String) : String := escape id

/-- The Lean name of a type parameter: `τ` before the spec name, which is
ASCII, so a spec variable of the parameter's type (conventionally named
like it) cannot shadow it. -/
def tparamName (id : String) : String := escape ("τ" ++ id)

/-- The Lean name of a spec function `$f`. -/
def funcName (id : String) : String := "«$" ++ id ++ "»"

/-- The Lean name of a relation. -/
def relName (id : String) : String := escape id

/-- The Lean name of a struct field. -/
def fieldName (a : Atom.t) : String := escape (atomName a)

/-- The suffix of an iteration dimension. -/
def iterSuffix : iter → String
  | .Opt => "?"
  | .List => "*"

/-- The Lean name of a variable with its dimensions. -/
def varName (id : String) (iters : List iter) : String :=
  escape (id ++ String.join (iters.map iterSuffix))

/-- The Lean name of a rule, for constructors of the relation's inductive. -/
def ruleName (group path : String) : String :=
  escape (if group == path || group == "" then path else group ++ "/" ++ path)

/-- The module components of a spec file relative to the spec root: the
path components verbatim, without the `.watsup` extension, each quoted
when it is not an identifier. -/
def moduleComponents (file : String) (specRoot : String) : List String :=
  let rel := if file.startsWith specRoot then String.ofList (file.toList.drop specRoot.length)
    else file
  let rel := if rel.endsWith ".watsup" then String.ofList (rel.toList.take (rel.length - 7))
    else rel
  (rel.splitOn "/").filter (· != "") |>.map escape

/-- The module name of a spec file, dotted. -/
def moduleName (file : String) (specRoot : String) : String :=
  ".".intercalate (moduleComponents file specRoot)

/-- The common directory prefix of the spec files, with its trailing slash. -/
def specRoot (files : List String) : String :=
  match files with
  | [] => ""
  | f :: fs =>
    let dir (p : String) : List String := (p.splitOn "/").dropLast
    let common := fs.foldl (fun acc p => commonPrefix acc (dir p)) (dir f)
    if common.isEmpty then "" else "/".intercalate common ++ "/"
where
  /-- The longest common prefix of two lists. -/
  commonPrefix : List String → List String → List String
    | a :: as, b :: bs => if a == b then a :: commonPrefix as bs else []
    | _, _ => []

end P4SpecTec.Codegen.Names
