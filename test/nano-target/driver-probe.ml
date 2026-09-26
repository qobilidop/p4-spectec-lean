(* Direct observations of the original driver, with an explicit relation stub.
   Fresh process per request; no replacement driver or packet normalization. *)
module O = Backend_sim.Core.Object
module V = Runtime.Value
module T = Runtime.Type.Typ
module Run = Runtime.Dynamic_Runner.Signature
module Spec = Backend_sim.Spec.Make ()
module Target = Backend_sim.Nano_switch.Pipe.Make (Spec)
open Util.Source

let var name = T.Make.var (name $ no_region) []
let value x = Lang.Il.value_to_yojson x
let packet (port, payload) = `List [`Int port; `String payload]
let observe request =
  let open Yojson.Safe.Util in
  let decision = request |> member "decision" |> to_string in
  let payload = request |> member "payload" |> to_string in
  let port = request |> member "port" |> to_int in
  let called = ref false in
  Spec.Rel.register (fun name args ->
    called := true;
    assert (name = "NanoSwitch_drive");
    (match args with
    | [ctx; state] ->
        assert (V.Get.bool ctx = false);
        assert (state.note.typ = (var "objectState").it);
        assert (V.Get.extern state =
          `List [`String "PacketIn"; O.PacketIn.to_yojson (O.PacketIn.init payload)])
    | _ -> failwith "wrong driver arguments");
    ignore (Interface.NanoP4.call_builtin (fun _ -> ())
      ("fresh_typeId" $ no_region) [] []);
    let atom = Domain.Mixfix.Atom (Domain.Atom.Keyword "FORWARD" $ no_region) in
    let result = match decision with
      | "forward" -> V.Make.case (var "decision") atom
      | "drop" -> V.Make.case (var "decision")
          (Domain.Mixfix.Atom (Domain.Atom.Keyword "DROP" $ no_region))
      | "noncase" -> V.Make.bool true
      | "sequence" -> V.Make.case (var "decision") (Domain.Mixfix.Seq [atom])
      | "unmatch" -> raise (Run.ExternError (Run.Unmatch []))
      | "abort" -> raise (Run.ExternError
          (Run.abort ~source:"driver-probe" no_region "requested failure"))
      | "arity" -> V.Make.bool true
      | _ -> failwith "unknown decision" in
    if decision = "arity" then [result] else [result; V.Make.bool true]);
  let fields () = [("called", `Bool !called);
    ("counterAfter", `Int (Interface.NanoP4.checkpoint ()))] in
  try
    let ctx, arch, txs = Target.drive_pipe (V.Make.bool false) (V.Make.text "arch")
      (port, payload) in
    `Assoc (fields () @ [("class", `String "pass");
      ("outputs", `List [value ctx; value arch]);
      ("txs", `List (List.map packet txs))])
  with
  | Assert_failure _ -> `Assoc (fields () @ [("class", `String "assertion")])
  | Run.ExternError (Run.Unmatch _) ->
      `Assoc (fields () @ [("class", `String "unmatch")])
  | Run.ExternError (Run.Abort _) ->
      `Assoc (fields () @ [("class", `String "abort")])

let () =
  if Array.length Sys.argv <> 2 then failwith "expected one JSON request";
  print_endline (Yojson.Safe.to_string (observe (Yojson.Safe.from_string Sys.argv.(1))))
