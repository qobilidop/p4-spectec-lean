(* Bounded type-runtime outcomes from the pinned upstream implementation. *)

open Util.Source
module IL = Lang.Il
module T = Runtime.Type

let p x = x $ no_region
let param x = p x
let bool = p IL.BoolT
let text = p IL.TextT
let var ?(args = []) x = p (IL.VarT (p x, args))
let find tid =
  match tid.it with
  | "BoolAlias" -> Some (T.Typdef.Defined ([], p (IL.PlainT bool)))
  | "BoundAlias" -> Some (T.Typdef.Defined ([], p (IL.PlainT (var "A"))))
  | "UnaryAlias" ->
      Some (T.Typdef.Defined ([param "X"], p (IL.PlainT (var "X"))))
  | "UnaryStruct" ->
      Some (T.Typdef.Defined ([param "X"], p (IL.StructT [])))
  | "DuplicateAlias" ->
      Some (T.Typdef.Defined ([param "X"; param "X"], p (IL.PlainT (var "X"))))
  | "A" -> Some (T.Typdef.Defined ([], p (IL.PlainT bool)))
  | _ -> None

let outcome name thunk =
  let result =
    try `Assoc ["class", `String "ok"; "value", `Bool (thunk ())]
    with
    | Error.RuntimeError (_, message) ->
        `Assoc ["class", `String "error"; "message", `String message]
    | Invalid_argument message ->
        `Assoc ["class", `String "error"; "message", `String message]
  in
  `Assoc ["name", `String name; "result", result]

let cases =
  [ outcome "alias" (fun () -> T.Equiv.equiv_typ find (var "BoolAlias") bool);
    outcome "alias-argument" (fun () ->
        T.Equiv.equiv_typ find (var ~args:[text] "UnaryAlias") text);
    outcome "alias-arity" (fun () ->
        T.Equiv.equiv_typ find (var "UnaryAlias") bool);
    outcome "unknown" (fun () ->
        T.Equiv.equiv_typ find (var "Missing") bool);
    outcome "alpha" (fun () ->
        T.Equiv.equiv_functyp find [param "X"] [var "X"] (var "X")
          [param "Y"] [var "Y"] (var "Y"));
    outcome "different-return" (fun () ->
        T.Equiv.equiv_functyp find [param "X"] [var "X"] (var "X")
          [param "Y"] [var "Y"] bool);
    outcome "alias-binder-collision" (fun () ->
        T.Equiv.equiv_functyp find [param "A"] [var "BoundAlias"] bool
          [param "B"] [bool] bool);
    outcome "higher-order" (fun () ->
        T.Equiv.equiv_functyp find [param "X"] [var ~args:[bool] "X"] bool
          [param "Y"] [var ~args:[bool] "Y"] bool);
    outcome "binder-arity" (fun () ->
        T.Equiv.equiv_functyp find [param "X"] [var "X"] bool [] [bool] bool);
    outcome "iter-error-before-iter-mismatch" (fun () ->
        T.Equiv.equiv_typ find (p (IL.IterT (var "Missing", IL.Opt)))
          (p (IL.IterT (bool, IL.List))));
    outcome "notation-error-before-later-atom-mismatch" (fun () ->
        let open Domain.Mixfix in
        let a = p (Seq [Arg (var "Missing"); Atom (p (Domain.Atom.Keyword "LEFT"))]) in
        let b = p (Seq [Arg bool; Atom (p (Domain.Atom.Keyword "RIGHT"))]) in
        T.Equiv.equiv_nottyp find a b);
    outcome "sub-arity-matched" (fun () ->
        Runtime.Value.Match.sub_ find (fun _ -> None) (var "UnaryAlias")
          (Runtime.Value.Make.bool true));
    outcome "sub-arity-unmatched-shape" (fun () ->
        Runtime.Value.Match.sub_ find (fun _ -> None) (var "UnaryStruct")
          (Runtime.Value.Make.bool true));
    outcome "duplicate-binding-last-wins" (fun () ->
        T.Equiv.equiv_typ find (var ~args:[bool; text] "DuplicateAlias") text) ]

let () = print_endline (Yojson.Safe.to_string (`List cases))
