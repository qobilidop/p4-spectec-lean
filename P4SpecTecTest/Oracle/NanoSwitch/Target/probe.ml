module O = Backend_sim.Core.Object
module V = Runtime.Value
module T = Runtime.Type.Typ
module Run = Runtime.Dynamic_Runner.Signature
module Spec = Backend_sim.Spec.Make ()
module Target = Backend_sim.Nano_switch.Pipe.Make (Spec)
open Util.Source

exception Decode

let decode = function Ok x -> x | Error _ -> raise Decode
let member key json = Yojson.Safe.Util.member key json
let integer key json = Yojson.Safe.Util.to_int (member key json)
let text key json = Yojson.Safe.Util.to_string (member key json)
let var name = T.Make.var (name $ no_region) []
let pass value = `Assoc [ ("class", `String "pass"); ("value", value) ]
let failure name = `Assoc [ ("class", `String name) ]
let require_local (scope : V.t) =
  match scope.it with
  | Lang.Il.CaseV (Domain.Mixfix.Atom a) -> assert (a.it = Domain.Atom.Keyword "LOCAL")
  | _ -> failwith "wrong LOCAL callback shape"

let observe json =
  try
    let value =
      match text "op" json with
      | "hex" -> O.string_to_bits (text "text" json) |> O.bits_to_yojson
      | "bits_string" ->
          member "bits" json |> O.bits_of_yojson |> decode |> O.bits_to_string
          |> fun s -> `String s
      | "signed" ->
          member "bits" json |> O.bits_of_yojson |> decode |> O.bits_to_int_signed
          |> Bigint.to_string |> fun s -> `String s
      | "unsigned" ->
          member "bits" json |> O.bits_of_yojson |> decode |> O.bits_to_int_unsigned
          |> Bigint.to_string |> fun s -> `String s
      | "int_signed" ->
          O.int_to_bits_signed (Bigint.of_string (text "value" json)) (integer "size" json)
          |> O.bits_to_yojson
      | "int_unsigned" ->
          O.int_to_bits_unsigned (Bigint.of_string (text "value" json)) (integer "size" json)
          |> O.bits_to_yojson
      | "init" -> O.PacketIn.init (text "text" json) |> O.PacketIn.to_yojson
      | "decode" -> member "packet" json |> O.PacketIn.of_yojson |> decode |> O.PacketIn.to_yojson
      | "parse" ->
          let pkt = member "packet" json |> O.PacketIn.of_yojson |> decode in
          let pkt, bits = O.PacketIn.parse pkt (integer "size" json) in
          `List [ O.PacketIn.to_yojson pkt; O.bits_to_yojson bits ]
      | "payload" ->
          member "packet" json |> O.PacketIn.of_yojson |> decode |> O.PacketIn.payload
          |> O.bits_to_yojson
      | "payload_bytes" ->
          member "packet" json |> O.PacketIn.of_yojson |> decode |> O.PacketIn.payload_bytes
          |> Array.to_list |> List.map (fun n -> `String (Bigint.to_string n))
          |> fun xs -> `List xs
      | "target" ->
          let trace = ref [] in
          Spec.Func.register (fun name typs values ->
            trace := !trace @ [ `String name ];
            if typs <> [] then failwith "unexpected type arguments";
            match name, values with
            | "find_var_e", [scope; ctx; hdr] ->
                require_local scope;
                assert (V.Get.bool ctx = false && V.Get.text hdr = "hdr");
                V.Make.nat (Bigint.of_int 10)
            | "write_value_from_bits", [hdr; bits] ->
                assert (V.Get.num hdr = `Nat (Bigint.of_int 10));
                let bits = V.Get.list bits |> List.map V.Get.bool in
                assert (List.length bits = 24 && List.for_all Fun.id bits);
                V.Make.nat (Bigint.of_int 42)
            | "update_var_e", [scope; ctx; name; hdr] ->
                require_local scope;
                assert (V.Get.bool ctx = false && V.Get.text name = "hdr"
                  && V.Get.num hdr = `Nat (Bigint.of_int 42));
                V.Make.bool true
            | _ -> failwith "unexpected callback");
          let state = V.Make.extern (var "objectState")
            (`List [`String "PacketIn"; member "packet" json]) in
          let receiver = V.Make.("PACKET typeId objectState" <| [text "packet_in"; state]
            <<| "value") in
          let params = V.Make.list (T.Make.list (var "nameIR")) [V.Make.text "hdr"] in
          let outputs = Target.eval_extern_method_call
            [V.Make.bool false; receiver; V.Make.text "extract"; params] in
          (match outputs with
          | [state; ctx] -> `Assoc [ ("objectState", V.Get.extern state);
              ("context", `Bool (V.Get.bool ctx)); ("callbacks", `List !trace) ]
          | _ -> failwith "wrong output arity")
      | name -> failwith ("unknown operation " ^ name)
    in
    pass value
  with
  | Decode -> failure "decode"
  | Assert_failure _ -> failure "assertion"
  | Invalid_argument _ -> failure "invalidArgument"
  | Run.ExternError _ -> failure "abort"

let () =
  if Array.length Sys.argv <> 2 then failwith "expected one JSON request";
  let result = observe (Yojson.Safe.from_string Sys.argv.(1)) in
  print_endline (Yojson.Safe.to_string result)
