(* Observations from the pinned upstream implementation, not expected answers. *)
open Util.Source
open Lang
open Hints.Alter

let at x = x $ no_region
let hole = HoleH (at `Next)
let nth n = HoleH (at (`Num n))
let atom x = at x

let wrap tid first second =
  let vc = Domain.Mixfix.Seq [
    Domain.Mixfix.Atom (atom (Domain.Atom.Keyword "WRAP"));
    Domain.Mixfix.Arg first; Domain.Mixfix.Arg second]
  in
  Runtime.Value.Make.case (at (Il.VarT (at tid, []))) vc

let value tid = wrap tid (Runtime.Value.Make.text "A") (Runtime.Value.Make.text "B")

let rec expression = function
  | TextH s -> at (El.TextE s)
  | AtomH a -> at (El.AtomE a)
  | SeqH hs -> at (El.SeqE (List.map expression hs))
  | BrackH (a, h, b) -> at (El.BrackE (a, expression h, b))
  | HoleH {it = `Next; _} -> at (El.HoleE `Next)
  | HoleH {it = `Num n; _} -> at (El.HoleE (`Num n))
  | FuseH (a, b) -> at (El.FuseE (expression a, no_region, expression b))
  | OtherH e -> e

let spec hint =
  let v = value "alpha" in
  let nottyp = match v.it with
    | Il.CaseV vc -> Domain.Mixfix.map (fun _ -> at Il.TextT) vc
    | _ -> assert false
  in
  let h = at {El.hintid = at "print"; hintexp = expression hint} in
  let typcase = (at nottyp, at (at "alpha", []), [h]) in
  [at (Al.TypD (at "alpha", [], at (Il.VariantT [typcase]), []))]

let output name spec value =
  let henv = P4.Unparse.hints_of_spec_al spec in
  let printed = Format.asprintf "%a" (P4.Unparse.pp_value henv) value in
  `Assoc ["name", `String name; "spec", Al.spec_to_yojson spec;
          "value", Il.value_to_yojson value; "output", `String printed]

let () =
  let cases = [
    "next-numbered", SeqH [hole; nth 1; hole; nth 0];
    "fuse", FuseH (hole, FuseH (TextH "", nth 1));
    "seq-empty", SeqH [hole; TextH ""; hole];
    "brack-empty-text", BrackH (atom Domain.Atom.LBrace, TextH "", atom Domain.Atom.RBrace);
    "brack-empty-atom", BrackH (atom Domain.Atom.LBrace,
      AtomH (atom (Domain.Atom.Tag "silent")), atom Domain.Atom.RBrace)]
  in
  let outputs = List.map (fun (name, hint) -> output name (spec hint) (value "alpha")) cases in
  let spec = spec (TextH "hinted") in
  let unsupported = Runtime.Value.Make.str (at Il.TextT) [] in
  let unicode_atom = Runtime.Value.Make.case (at (Il.VarT (at "unicode", [])))
    (Domain.Mixfix.Atom (atom (Domain.Atom.Keyword "MIXÉΩ"))) in
  let outputs = outputs @ [
    output "type-alpha" spec (value "alpha");
    output "type-beta-default" spec (value "beta");
    output "empty-table-default" [] (value "alpha");
    output "unused-unsupported-argument" spec
      (wrap "alpha" unsupported (Runtime.Value.Make.text "B"));
    output "nested-value-hint" spec
      (wrap "beta" (value "alpha") (Runtime.Value.Make.text "B"));
    output "unicode-text" [] (Runtime.Value.Make.text "éΩ\n");
    output "ascii-only-atom-case" [] unicode_atom]
  in
  print_endline (Yojson.Safe.to_string (`List outputs))
