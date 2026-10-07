import Lean.Data.Json.FromToJson.Basic
import P4SpecTec.Lang.Il.Json

/-!
Not a mirror: this module is our own, placed beside the decoders it inverts.

JSON encoders for the IL values and types, following the `[@@deriving yojson]` encoding of
`p4spec/lib/lang/il/ast.ml` and the hand-written `Mixfix.mixop_to_yojson`, exactly as
`P4SpecTec.Lang.Il.Json` decodes them. A target that keeps IL values inside its serialized
state (the v1model registers and its scheduled packets) encodes them with these; the
decoders read them back. Natural numbers and integers are encoded as strings, as upstream's
`Bigint` is.
-/

namespace P4SpecTec.Lang.Il.Encode

open Lean (Json)
open P4SpecTec.Util.Source
open P4SpecTec.Lang.Xl
open P4SpecTec.Domain

/-- An integer as a JSON number. -/
def jint (i : Int) : Json := Lean.toJson i

/-- A variant with its arguments. -/
def variant (c : String) (args : List Json) : Json := .arr (#[Json.str c] ++ args.toArray)

/-- Encode a position. -/
def pos (p : pos) : Json :=
  Json.mkObj [("file", .str p.file), ("line", jint p.line), ("column", jint p.column)]

/-- Encode a region. -/
def region (r : region) : Json := Json.mkObj [("left", pos r.left), ("right", pos r.right)]

/-- Encode an `info` record. -/
def info {α β γ : Type} (eit : α → Json) (enote : β → Json) (eat : γ → Json)
    (x : info α β γ) : Json :=
  Json.mkObj [("it", eit x.it), ("note", enote x.note), ("at", eat x.«at»)]

/-- Encode a phrase, whose note is `null`. -/
def phrase {α : Type} (e : α → Json) (x : phrase α) : Json := info e (fun _ => .null) region x

/-- Encode a big integer as upstream's `Bigint` string. -/
def bigint (i : Int) : Json := .str (toString i)

/-- Encode `Num.t`. -/
def num : Num.t → Json
  | .Nat n => variant "Nat" [bigint n]
  | .Int i => variant "Int" [bigint i]

/-- Encode `Num.typ`. -/
def numtyp : Num.typ → Json
  | .NatT => variant "NatT" []
  | .IntT => variant "IntT" []

/-- Encode `id`. -/
def id (i : id) : Json := phrase Json.str i

/-- Encode `Atom.t`. -/
def atom' : Atom.t → Json
  | .Keyword s => variant "Keyword" [.str s]
  | .Tag s => variant "Tag" [.str s]
  | .Operator s => variant "Operator" [.str s]
  | .Sub => variant "Sub" [] | .Sup => variant "Sup" []
  | .Turnstile => variant "Turnstile" [] | .Tilesturn => variant "Tilesturn" []
  | .Arrow => variant "Arrow" [] | .ArrowSub => variant "ArrowSub" []
  | .DoubleArrowSub => variant "DoubleArrowSub" []
  | .DoubleArrowLong => variant "DoubleArrowLong" []
  | .SqArrow => variant "SqArrow" [] | .SqArrowStar => variant "SqArrowStar" []
  | .Dot => variant "Dot" [] | .Dot2 => variant "Dot2" [] | .Dot3 => variant "Dot3" []
  | .Semicolon => variant "Semicolon" [] | .Colon => variant "Colon" []
  | .ColonEq => variant "ColonEq" []
  | .Tilde2 => variant "Tilde2" [] | .Backslash => variant "Backslash" []
  | .LAngle => variant "LAngle" [] | .RAngle => variant "RAngle" []
  | .LParen => variant "LParen" [] | .RParen => variant "RParen" []
  | .LBrack => variant "LBrack" [] | .RBrack => variant "RBrack" []
  | .LBrace => variant "LBrace" [] | .RBrace => variant "RBrace" []

/-- Encode `atom`. -/
def atom (a : atom) : Json := phrase atom' a

/-- Encode a mixfix given an encoder for the holes. -/
partial def mixfix {α : Type} (e : α → Json) : Mixfix.t α → Json
  | .Arg x => variant "Arg" [e x]
  | .Atom a => variant "Atom" [atom a]
  | .Brack l m r => variant "Brack" [atom l, mixfix e m, atom r]
  | .Infix l a r => variant "Infix" [mixfix e l, atom a, mixfix e r]
  | .Seq ms => variant "Seq" [.arr (ms.map (mixfix e)).toArray]

/-- Encode `iter`. -/
def iter : iter → Json
  | .Opt => variant "Opt" []
  | .List => variant "List" []

mutual

/-- Encode `typ'`. -/
partial def typ' : typ' → Json
  | .BoolT => variant "BoolT" []
  | .NumT t => variant "NumT" [numtyp t]
  | .TextT => variant "TextT" []
  | .VarT i ts => variant "VarT" [id i, .arr (ts.map typ).toArray]
  | .TupleT ts => variant "TupleT" [.arr (ts.map typ).toArray]
  | .IterT t i => variant "IterT" [typ t, iter i]
  | .FuncT tps ts t =>
    variant "FuncT" [.arr (tps.map id).toArray, .arr (ts.map typ).toArray, typ t]

/-- Encode `typ`. -/
partial def typ (t : typ) : Json := phrase typ' t

end

/-- Encode `vnote`. -/
def vnote (n : vnote) : Json :=
  Json.mkObj [("vid", jint n.vid), ("typ", typ' n.typ), ("vhash", jint n.vhash)]

mutual

/-- Encode `value'`. -/
partial def value' : value' → Json
  | .BoolV b => variant "BoolV" [.bool b]
  | .NumV n => variant "NumV" [num n]
  | .TextV s => variant "TextV" [.str (s.toString?.getD "")]
  | .StructV fs => variant "StructV" [.arr (fs.map fun (a, v) => .arr #[atom a, value v]).toArray]
  | .CaseV m => variant "CaseV" [mixfix value m]
  | .TupleV vs => variant "TupleV" [.arr (vs.map value).toArray]
  | .OptV v => variant "OptV" [match v with | some x => value x | none => .null]
  | .ListV vs => variant "ListV" [.arr (vs.map value).toArray]
  | .FuncV i => variant "FuncV" [id i]
  | .ExternV x => variant "ExternV" [x]

/-- Encode `value`. -/
partial def value (v : value) : Json := info value' vnote region v

end

end P4SpecTec.Lang.Il.Encode
