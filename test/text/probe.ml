(* Executable observations from the pinned upstream text builtin wrappers. *)

module Value = Runtime.Value
module Texts = Builtin.Texts
open Util.Source

let hex_of_string s =
  String.to_seq s |> List.of_seq
  |> List.map (fun c -> Printf.sprintf "%02x" (Char.code c))
  |> String.concat ""

let json_text v =
  `Assoc ["textHex", `String (hex_of_string (Value.Get.text v))]

let json_texts v =
  `Assoc ["textsHex", `List (List.map
    (fun item -> `String (hex_of_string (Value.Get.text item))) (Value.Get.list v))]

let json_int v =
  let n = match Value.Get.num v with `Nat n | `Int n -> n in
  `Assoc ["intDecimal", `String (Bigint.to_string n)]

let json_arg (v : Value.t) = match v.it with
  | Lang.Il.TextV s -> `Assoc ["textHex", `String (hex_of_string s)]
  | Lang.Il.NumV (`Nat n | `Int n) ->
      `Assoc ["intDecimal", `String (Bigint.to_string n)]
  | _ -> assert false

let observe name operation args call project =
  let additions = ref 0 in
  let result =
    try
      let value = call (fun _ -> incr additions) Util.Source.no_region [] args in
      `Assoc ["status", `String "ok"; "value", project value]
    with
    | Builtin.Error.BuiltinError _ ->
        `Assoc ["status", `String "builtin_error"]
    | Assert_failure _ -> `Assoc ["status", `String "assert_failure"]
    | Invalid_argument _ -> `Assoc ["status", `String "invalid_argument"]
    | Failure _ -> `Assoc ["status", `String "failure"]
    | _ -> `Assoc ["status", `String "other"]
  in
  `Assoc ["name", `String name; "operation", `String operation;
          "args", `List (List.map json_arg args);
          "additions", `Int !additions; "result", result]

let text name operation call project strings =
  observe name operation (List.map Value.Make.text strings) call project

let number name s =
  text name "text_to_int" Texts.text_to_int json_int [s]

let split name s sep =
  text name "split_text" Texts.split_text json_texts [s; sep]

let prefix name s p =
  text name "strip_prefix" Texts.strip_prefix json_text [s; p]

let suffix name s p =
  text name "strip_suffix" Texts.strip_suffix json_text [s; p]

let spaces name s =
  text name "strip_all_whitespace" Texts.strip_all_whitespace json_text [s]

let to_text name n =
  observe name "int_to_text" [Value.Make.int (Bigint.of_int n)]
    Texts.int_to_text json_text

let () =
  let numbers = [
    "decimal-negative", "-42"; "decimal-positive", "+42";
    "hex-upper", "0xFF"; "hex-minus", "-0Xf";
    "binary-plus", "+0b101"; "octal", "0o77";
    "underscores", "1__2_"; "hex-underscores", "0xA_B";
    "empty", ""; "bare-plus", "+"; "bare-minus", "-";
    "bare-prefix", "0x"; "bare-negative-prefix", "-0x";
    "leading-underscore", "_1"; "prefix-underscore", "0x_1";
    "invalid-binary", "0b102"; "invalid-octal", "0o8";
    "invalid-hex", "0xG"; "bad-sign", "--1";
    "leading-space", " 2"; "trailing-space", "2 ";
    "unicode", "\xc3\xa9"; "invalid-utf8", "\xff";
    "embedded-nul", "12\0003";
    "large", "123456789012345678901234567890"]
  in
  let numeric_cases = List.map (fun (name, s) -> number name s) numbers in
  let text_cases = [
    to_text "render-negative" (-3); to_text "render-zero" 0;
    to_text "render-positive" 3;
    split "split-ascii" "a,b,,c" ",";
    split "split-empty" "" ",";
    split "split-utf8-byte" "\xc3\xa9" "\xc3";
    split "split-nul-invalid" "\000\xff\000" "\000";
    split "split-multibyte-separator" "a" "\xc3\xa9";
    split "split-empty-separator" "a" "";
    prefix "prefix-ascii" "hello" "he";
    prefix "prefix-utf8-byte" "\xc3\xa9" "\xc3";
    prefix "prefix-empty" "hello" "";
    prefix "prefix-mismatch" "hello" "x";
    suffix "suffix-ascii" "hello" "lo";
    suffix "suffix-utf8-byte" "\xc3\xa9" "\xa9";
    suffix "suffix-empty" "hello" "";
    suffix "suffix-mismatch" "hello" "x";
    spaces "spaces-ascii" "a b  c";
    spaces "spaces-invalid" "\xff \t\000";
    spaces "spaces-utf8" "\xc3\xa9 \xc3\xa9";
    spaces "spaces-empty" ""]
  in
  print_endline (Yojson.Safe.to_string (`List (numeric_cases @ text_cases)))
