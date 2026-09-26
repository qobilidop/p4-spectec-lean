(* Original shared verify and Nano extern dispatch, not a replacement target. *)
open Util.Source
module V = Runtime.Value
module T = Runtime.Type.Typ
module Run = Runtime.Dynamic_Runner.Signature
module Spec = Backend_sim.Spec.Make ()
module Core = Backend_sim.Core.Func.Make (Spec.Func)
module Target = Backend_sim.Nano_switch.Pipe.Make (Spec)
module Extern = Backend_sim.Extern.Make (Target)
module Interp = Interp_al.Interp.Make (Interface.NanoP4) (Extern) ()

let var s = T.Make.var (s $ no_region) []
let values vs = `List (List.map Lang.Il.value_to_yojson vs)
let text j key = Yojson.Safe.Util.(j |> member key |> to_string)
let check_value kind =
  let b = V.Make.bool (kind <> "false") in
  match kind with
  | "bare" -> b
  | "inner" -> V.Make.("_B bool" <| [nat (Bigint.of_int 1)] <<| "boolValue")
  | "tag" -> V.Make.("B bool" <| [b] <<| "boolValue")
  | _ -> V.Make.("_B bool" <| [b] <<| "boolValue")
let signal = V.Make.extern (var "errorValue") (`Assoc [("raw", `String "signal")])
let ctx = V.Make.bool false
let arch = V.Make.extern (var "archState") (`Assoc [("kept", `String "arch")])
let params xs = V.Make.list (T.Make.list (var "nameIR")) (List.map V.Make.text xs)

let observe request =
  let calls = ref [] in
  let check = text request "check" in
  let failure = text request "failure" in
  Spec.Func.register (fun name typs args ->
    calls := !calls @ [`Assoc [("name", `String name);
      ("types", `List (List.map Lang.Il.typ_to_yojson typs)); ("args", values args)]];
    ignore (Interface.NanoP4.call_builtin (fun _ -> ())
      ("fresh_typeId" $ no_region) [] []);
    let index = List.length !calls in
    if failure = "unmatch" ^ string_of_int index then
      raise (Run.ExternError (Run.Unmatch []));
    if failure = "abort" ^ string_of_int index then
      raise (Run.ExternError (Run.abort ~source:"verify-probe" no_region "requested"));
    if index = 1 then check_value check else signal);
  let args = match text request "shape" with
    | "arity" -> []
    | "name" -> [ctx; arch; V.Make.bool false; params []]
    | "list" -> [ctx; arch; V.Make.text "verify"; V.Make.bool false]
    | "element" -> [ctx; arch; V.Make.text "verify";
        V.Make.list (T.Make.list (var "nameIR")) [V.Make.bool false]]
    | "order" -> [ctx; arch; V.Make.text "verify"; params ["toSignal"; "check"]]
    | "static_assert" -> [ctx; arch; V.Make.text "static_assert"; params ["check"]]
    | _ -> [ctx; arch; V.Make.text "verify"; params ["check"; "toSignal"]] in
  let fields cls = [("class", `String cls); ("calls", `List !calls);
    ("counterAfter", `Int (Interface.NanoP4.checkpoint ()))] in
  try
    let outputs = match text request "entry" with
      | "core" -> let c, a, r = Core.verify ctx arch in [c; a; r]
      | "function" -> Target.eval_extern_func_call args
      | relation -> (match Target.eval_extern_rel relation args with
          | Run.Pass vs -> vs | Run.Fail f -> raise (Run.ExternError f)) in
    `Assoc (fields "pass" @ [("outputs", values outputs)])
  with
  | Error.RuntimeError (_, message) ->
      `Assoc (fields "runtimeError" @ [("message", `String message)])
  | Run.ExternError (Run.Abort _) -> `Assoc (fields "abort")
  | Run.ExternError (Run.Unmatch _) -> `Assoc (fields "unmatch")

let reachability spec_dir =
  let spec = match Pass.algo [spec_dir] with Ok s -> s | Error _ -> failwith "bad spec" in
  let external_names = List.filter_map (fun d -> match d.it with
    | Lang.Al.ExternRelD (id, _, _, _) -> Some id.it | _ -> None) spec in
  (match Interp.init ~cache:false ~det:false ~guard:false spec with
   | Ok () -> () | Error _ -> failwith "AL initialization failed");
  let args = ref [] in
  Spec.Func.register (fun _ _ vs -> args := vs; V.Make.bool false);
  ignore (Spec.Func.find_var_e_local ctx "check");
  let before = Interface.NanoP4.checkpoint () in
  let outcome = match Interp.eval_func "find_var_e" [] !args with
    | Run.Pass _ -> "pass" | Run.Fail (Run.Unmatch _) -> "unmatch"
    | Run.Fail (Run.Abort _) -> "abort" in
  `Assoc [("externRelations", `List (List.map (fun s -> `String s) external_names));
    ("mode", `String "AL"); ("cache", `Bool false); ("det", `Bool false);
    ("guard", `Bool false);
    ("counterBefore", `Int before);
    ("counterAfter", `Int (Interface.NanoP4.checkpoint ()));
    ("fullP4GetterAgainstNano", `String outcome)]

let () =
  let result = match Array.to_list Sys.argv with
    | [_; "reachability"; spec_dir] -> reachability spec_dir
    | [_; request] -> observe (Yojson.Safe.from_string request)
    | _ -> failwith "expected request or reachability SPEC" in
  print_endline ("OBSERVATION " ^ Yojson.Safe.to_string result)
