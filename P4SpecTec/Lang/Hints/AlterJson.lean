import P4SpecTec.Lang.Hints.Alter
import P4SpecTec.Lang.Il.Json

/-!
Not a mirror: decode the EL hint-expression subset used by alteration hints
from the unchanged upstream JSON export. Unsupported EL constructors fail
explicitly until the EL itself is ported.
-/

namespace P4SpecTec.Lang.Hints.AlterJson

open Lean (Json)
open P4SpecTec.Util.Source
open P4SpecTec.Util.Yojson
open P4SpecTec.Lang.Hints

/-- Decode an EL expression phrase into an alteration. The supported cases
are precisely those handled by upstream `Alter.init` before its `OtherH`
fallback. -/
partial def decode : D Alter.t := fun j => do
  let e ← phrase (fun x => pure x) j
  let (c, args) ← variant e.it
  match c, args with
  | "TextE", #[s] => .TextH <$> str s
  | "AtomE", #[a] => .AtomH <$> Lang.Il.Json.atom a
  | "SeqE", #[es] => .SeqH <$> list decode es
  | "BrackE", #[left, inner, right] => do
    pure (.BrackH (← Lang.Il.Json.atom left) (← decode inner)
      (← Lang.Il.Json.atom right))
  | "HoleE", #[h] =>
    match ← variant h with
    | ("Next", #[]) => pure (.HoleH (mkPhrase .Next e.at))
    | ("Num", #[idx]) => pure (.HoleH (mkPhrase (.Num (← int idx)) e.at))
    | _ => fail "unsupported alteration hole" h
  | "FuseE", #[left, separator, right] => do
    let _ ← region separator
    pure (.FuseH (← decode left) (← decode right))
  | _, _ => fail "unsupported alteration expression" e.it

/-- Decode the `hintexp` member of an exported EL hint record. -/
def ofHint : D Alter.t := fun j => do
  decode (← field j "hintexp")

end P4SpecTec.Lang.Hints.AlterJson
