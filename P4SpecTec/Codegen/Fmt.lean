import P4SpecTec.Util.ByteText

/-!
Building Lean source text. Terms are `Std.Format` with a flag saying
whether they need parentheses as arguments; declarations are formats
joined by blank lines; the printer wraps at the project's 100 columns.
-/

namespace P4SpecTec.Codegen

open Std (Format)

/-- A term: its text and whether it is atomic (needs no parentheses as an
argument or operand). -/
structure Term where
  /-- The text. -/
  fmt : Format
  /-- Whether it is an identifier, literal or bracketed form. -/
  atomic : Bool := false
  deriving Inhabited

namespace Term

/-- An atomic term from text. -/
def atom (s : String) : Term := ⟨Format.text s, true⟩

/-- A compound term from text. -/
def raw (f : Format) : Term := ⟨f, false⟩

/-- An atomic term from a format (already bracketed). -/
def atomicRaw (f : Format) : Term := ⟨f, true⟩

/-- A hard line break, honoured by `nest`. -/
def hardLine : Format := Format.text "\n"

/-- Parenthesise a term. -/
def paren (t : Term) : Term := ⟨Format.paren t.fmt, true⟩

/-- The term as an argument: parenthesised unless atomic. -/
def arg (t : Term) : Format := if t.atomic then t.fmt else Format.paren t.fmt

/-- Application. -/
def app (f : Term) (args : List Term) : Term :=
  if args.isEmpty then f
  else ⟨Format.group (Format.nest 2 (f.arg ++ Format.line ++
    Format.joinSep (args.map arg) Format.line)), false⟩

/-- Application of a named function. -/
def call (f : String) (args : List Term) : Term := app (atom f) args

/-- A binary operator. -/
def binop (op : String) (l r : Term) : Term :=
  ⟨Format.group (l.arg ++ " " ++ op ++ Format.line ++ r.arg), false⟩

/-- A prefix operator. -/
def prefixOp (op : String) (t : Term) : Term := ⟨Format.text op ++ t.arg, false⟩

/-- A tuple `(a, b, c)`; a single component is just that term. -/
def tuple : List Term → Term
  | [t] => t
  | ts => ⟨Format.paren (Format.joinSep (ts.map (·.fmt)) ("," ++ Format.line)), true⟩

/-- A list literal. -/
def list (ts : List Term) : Term :=
  ⟨Format.sbracket (Format.joinSep (ts.map (·.fmt)) ("," ++ Format.line)), true⟩

/-- A type ascription `(t : T)`. -/
def ascribe (t : Term) (ty : Term) : Term :=
  ⟨Format.paren (t.fmt ++ " : " ++ ty.fmt), true⟩

/-- A field projection `t.f`. -/
def proj (t : Term) (f : String) : Term := ⟨t.arg ++ "." ++ f, true⟩

/-- A structure instance `{ f := v, .. }`, optionally `{ s with .. }`. Every
field starts its own line at one column, as Lean's parser requires of
fields that do not share a line. -/
def structInst (base : Option Term) (fields : List (String × Term)) : Term :=
  let fs := Format.join (fields.map fun (f, v) =>
    hardLine ++ Format.text (f ++ " := ") ++ v.fmt ++ ",")
  let head := match base with
    | some b => Format.text "{ " ++ b.fmt ++ " with"
    | none => Format.text "{"
  ⟨head ++ Format.nest 2 fs ++ " }", true⟩

/-- A `fun x => body`. -/
def lam (binders : List String) (body : Term) : Term :=
  ⟨Format.group (Format.nest 2 (Format.text ("fun " ++ " ".intercalate binders ++ " =>") ++
    Format.line ++ body.fmt)), false⟩

/-- A `fun (pat : T) => body` with a binder that may break inside. -/
def lamF (binder : Format) (body : Term) : Term :=
  ⟨Format.group (Format.nest 2 (Format.text "fun " ++ binder ++ " =>" ++ Format.line ++ body.fmt)),
    false⟩

/-- An ascribed binder `(pat : T)` that breaks before the type. -/
def binder (pat : Format) (ty : Format) : Format :=
  Format.paren (Format.group (Format.nest 2 (pat ++ " :" ++ Format.line ++ ty)))

/-- A constructor or function applied to bare names, breaking between them. -/
def patApp (head : String) (args : List String) : Format :=
  Format.group (Format.nest 4 (Format.text head ++
    Format.join (args.map fun a => Format.line ++ Format.text a)))

/-- A `let pat := v` statement, with `| alt` when the pattern is refutable,
breaking after `:=`. -/
def letStmt (pat : Format) (v : Term) (alt : Option String := none) : Format :=
  Format.group (Format.nest 4 (Format.text "let " ++ pat ++ " :=" ++ Format.line ++ v.fmt ++
    (match alt with | some a => Format.text (" | " ++ a) | none => Format.nil)))

/-- A `have x := v` statement: a pure binding of a variable. `have`, not
`let`, because the monotonicity tactic of `partial_fixpoint` cannot
eliminate a match on a `let`-bound variable, and a `have` is a beta-redex
the proofs reduce. -/
def haveStmt (x : String) (v : Term) : Format :=
  Format.group (Format.nest 4 (Format.text s!"have {x} :=" ++ Format.line ++ v.fmt))

/-- A `let x ← m` statement, breaking after `←`. -/
def bindStmt (x : String) (m : Term) : Format :=
  Format.group (Format.nest 4 (Format.text s!"let {x} ←" ++ Format.line ++ m.fmt))

/-- A function type `A → B → C`, breaking after arrows. -/
def arrows (ts : List Format) : Format :=
  Format.group (Format.nest 2 (Format.joinSep ts (Format.text " →" ++ Format.line)))

/-- A declaration head `def name binders : T :=`; the result type moves to
its own line when the head does not fit. -/
def sig (name : String) (binders : Format) (ret : Format) : Format :=
  Format.group (Format.nest 4 (Format.text s!"def {name}" ++ binders ++ Format.line ++ ": " ++
    ret ++ " :="))

/-- A declaration head `def name binders : T :=` and its body on a new
line when the body does not fit. -/
def defn (head : Format) (body : Format) : Format :=
  Format.group (Format.nest 2 (head ++ " :=" ++ Format.line ++ body))

/-- A `match t with | p => e ...`. -/
def matchOn (scrut : Term) (arms : List (Format × Term)) : Term :=
  let armsF := arms.map fun (p, e) =>
    hardLine ++
      Format.group (Format.nest 2 (Format.text "| " ++ p ++ " =>" ++ Format.line ++ e.fmt))
  ⟨Format.nest 2 (Format.text "match " ++ scrut.fmt ++ " with" ++ Format.join armsF), false⟩

/-- A `do` block from statements. -/
def doBlock (stmts : List Format) : Term :=
  ⟨Format.nest 2 (Format.text "do" ++ Format.join (stmts.map (hardLine ++ ·))), false⟩

/-- `if c then a else b`. -/
def ite (c a b : Term) : Term :=
  ⟨Format.group (Format.text "if " ++ c.fmt ++ " then" ++ Format.nest 2 (Format.line ++ a.fmt) ++
    Format.line ++ "else" ++ Format.nest 2 (Format.line ++ b.fmt)), false⟩

/-- A string literal. -/
def strLit (s : String) : Term := atom s.quote

/-- A semantic text literal, preserving invalid UTF-8 as explicit bytes. -/
def textLit (s : ByteText) : Term :=
  match s.toString? with
  | some text => call "P4SpecTec.ByteText.ofString" [strLit text]
  | none =>
    let bytes := list (s.toBytes.toList.map fun b => atom (toString b.toNat))
    call "P4SpecTec.ByteText.ofBytes" [call "ByteArray.mk" [call "List.toArray" [bytes]]]

/-- A natural-number literal. -/
def natLit (n : Nat) : Term := atom (toString n)

/-- An integer literal. -/
def intLit (i : Int) : Term :=
  if i < 0 then ⟨Format.paren (Format.text (toString i)), true⟩ else atom (toString i)

end Term

/-- Render a format at the project width. -/
def render (f : Format) : String := f.pretty 100

/-- A blank-line-separated block of declarations. -/
def joinDecls (ds : List Format) : Format := Format.joinSep ds (Format.text "\n\n")

/-- A `mutual ... end` block. -/
def mutualBlock (ds : List Format) : Format :=
  match ds with
  | [d] => d
  | _ => Format.text "mutual\n\n" ++ joinDecls ds ++ "\n\nend"

/-- Indent a format by two spaces on every line after the first. -/
def indent (f : Format) : Format := Format.nest 2 f

end P4SpecTec.Codegen
