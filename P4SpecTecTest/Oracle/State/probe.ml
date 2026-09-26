(* Actual pinned AL interpreter observations, plus explicitly scoped primitive cases. *)

open Util.Source
module Run = Runtime.Dynamic_Runner.Signature
module Interface = Interface.SpecTec_AL
module Value = Runtime.Value
module AL = Lang.Al
module IL = Lang.Il

let p x = x $ no_region
let id x = p x
let typ = p IL.TextT
let e x note = x $$ (no_region, note)
let fresh = e (IL.CallE (id "fresh_typeId", [], [])) IL.TextT
let x = e (IL.VarE (id "x")) IL.TextT
let save = p (IL.LetPr (x, fresh))
let mismatch = p (IL.IfPr (e (IL.BoolE false) IL.BoolT))
let hard = p (IL.LetPr (e (IL.BoolE true) IL.BoolT, x))
let fun_def name premises =
  p (AL.FuncDecD (id name, [], [], typ,
    [p ([], fresh, premises); p ([], fresh, [])], None, []))
let negative_def name target =
  let tagged tag = e (IL.CatE (e (IL.TextE tag) IL.TextT, fresh)) IL.TextT in
  p (AL.FuncDecD (id name, [], [], typ,
    [p ([], tagged "first:",
      [p (IL.IfNotHoldPr (id target, Domain.Mixfix.Seq []))]);
     p ([], tagged "fallback:", [])], None, []))
let rel_def name premises =
  p (AL.RelD (id name, p (Domain.Mixfix.Seq []), [],
    [p (id "one", ([], [], []), [(id "path", premises, [])])], None, []))
let spec = [
  p (AL.BuiltinDecD (id "fresh_typeId", [], [], typ, []));
  fun_def "allocate" [];
  p (AL.ExternDecD (id "externalFresh", [], [], typ, []));
  fun_def "externalRetry" [p (IL.LetPr
    (x, e (IL.CallE (id "externalFresh", [], [])) IL.TextT))];
  p (AL.FuncDecD (id "through", [],
    [p (IL.DefP (id "f", [], [], typ))], typ,
    [p ([p (IL.DefA (id "f"))], e (IL.CallE (id "f", [], [])) IL.TextT, [])],
    None, []));
  fun_def "retry" [save; mismatch];
  fun_def "stop" [save; hard];
  rel_def "fails" [save; mismatch];
  rel_def "holds" [save];
  rel_def "errors" [save; hard];
  negative_def "negative" "fails";
  negative_def "negativeSuccess" "holds";
  negative_def "negativeError" "errors";
  p (AL.RelD (id "shared", p (Domain.Mixfix.Arg typ), [],
    [p (id "group", ([], [], [save]),
      [(id "reject", [mismatch], [x]); (id "accept", [], [x])])], None, []))
]

module Extern : Run.EXTERN = struct
  module Cache = struct
    let cache_on () = ()
    let cache_off () = ()
  end
  let eval_extern_rel _ _ = Run.Fail (Run.Unmatch [])
  let eval_extern_func _ _ _ =
    ignore (Interface.call_builtin (fun _ -> ()) (id "fresh_typeId") [] []);
    Run.Fail (Run.Unmatch [])
  let checkpoint () = 0
  let seff before after = before <> after
  let clear () = ()
  let init_mode _ = Ok ()
end

module Interp = Interp_al.Interp.Make (Interface) (Extern) ()

let text v = match v.it with IL.TextV s -> s | _ -> failwith "not text"
let json_result = function
  | Run.Pass v -> `Assoc ["status", `String "ok"; "text", `String (text v)]
  | Run.Fail (Run.Unmatch _) -> `Assoc ["status", `String "unmatch"]
  | Run.Fail (Run.Abort _) -> `Assoc ["status", `String "abort"]

let case ?(args = []) name operation =
  Interface.Builtin_SpecTec.init ();
  let result = Interp.eval_func operation [] args in
  `Assoc ["name", `String name; "scope", `String "full-al";
          "operation", `String operation; "seed", `Int 0;
          "result", json_result result;
          "counter", `Int (Interface.checkpoint ())]

let rel_case name operation =
  Interface.Builtin_SpecTec.init ();
  let result = Interp.eval_rel operation [] in
  let value = match result with
    | Run.Pass [v] -> `Assoc ["status", `String "ok"; "text", `String (text v)]
    | Run.Pass _ -> failwith "unexpected relation result arity"
    | Run.Fail (Run.Unmatch _) -> `Assoc ["status", `String "unmatch"]
    | Run.Fail (Run.Abort _) -> `Assoc ["status", `String "abort"]
  in
  `Assoc ["name", `String name; "scope", `String "full-al";
          "operation", `String operation; "seed", `Int 0;
          "result", value; "counter", `Int (Interface.checkpoint ())]

let session_case () =
  Interface.Builtin_SpecTec.init ();
  let first = Interp.eval_func "stop" [] [] in
  let first_counter = Interface.checkpoint () in
  let second = Interp.eval_func "allocate" [] [] in
  `Assoc ["name", `String "resume-after-failure"; "scope", `String "full-al-session";
          "seed", `Int 0;
          "first", json_result first; "firstCounter", `Int first_counter;
          "result", json_result second; "counter", `Int (Interface.checkpoint ())]

let primitive name counter targs args =
  let seed = !counter in
  let result =
    try Run.Pass (Builtin.Fresh.fresh_typeId counter (fun _ -> ()) no_region targs args)
    with Builtin.Error.BuiltinError _ -> Run.Fail (Run.Unmatch [])
  in
  `Assoc ["name", `String name; "scope", `String "primitive";
          "seed", `Int seed;
          "result", json_result result; "counter", `Int !counter]

let () =
  (match Interp.init ~cache:false ~det:false ~guard:false spec with
   | Ok () -> () | Error _ -> failwith "upstream AL spec initialization failed");
  let cases = [
    case "allocate" "allocate";
    case "extern-retry" "externalRetry";
    case ~args:[Value.Make.func (id "allocate") [] [] typ] "callback" "through";
    case "retry" "retry";
    case "stop" "stop";
    case "negative" "negative";
    case "negative-success" "negativeSuccess";
    case "negative-error" "negativeError";
    rel_case "shared" "shared";
    session_case ();
    primitive "fresh-valid" (ref 7) [] [];
    primitive "fresh-type-arity" (ref 7) [typ] [];
    primitive "fresh-value-arity" (ref 7) [] [Value.Make.text "argument"];
    primitive "fresh-wrap-max" (ref max_int) [] [];
    primitive "fresh-wrap-min" (ref min_int) [] []
  ] in
  print_endline (Yojson.Safe.to_string (`List cases))
