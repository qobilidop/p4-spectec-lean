(* One pinned full-P4 AL run. The Python driver starts a fresh process per relation. *)

module Run = Runtime.Dynamic_Runner.Signature
module Sim = Runtime.Sim.Signature

let diagnostic (d : Diagnostic.t) =
  let region, message = Diagnostic.region_msg d in
  `Assoc
    [ ("source", `String d.source);
      ("code", match d.code with None -> `Null | Some s -> `String s);
      ("message", `String message);
      ("region", `String (Util.Source.string_of_region region)) ]

let value_json = Lang.Il.value_to_yojson

let result_json = function
  | Run.Pass values ->
      `Assoc
        [ ("class", `String "pass");
          ("outputs", `List (List.map value_json values)) ]
  | Run.Fail (Run.Unmatch failtraces) ->
      `Assoc
        [ ("class", `String "unmatch");
          ("diagnostic",
           diagnostic (Run.diagnostic_of_failure (Run.Unmatch failtraces))) ]
  | Run.Fail (Run.Abort d) ->
      `Assoc [ ("class", `String "abort"); ("diagnostic", diagnostic d) ]

let emit json = print_endline (Yojson.Safe.to_string json)

let run spec_dir include_dir program relation =
  match Pass.algo [ spec_dir ] with
  | Error d ->
      emit (`Assoc [ ("phase", `String "spec"); ("diagnostic", diagnostic d) ]);
      exit 2
  | Ok spec -> (
      match Backend_sim.Build.build ~cache:true ~det:false ~guard:false
              (Run.AL spec) with
      | Error d ->
          emit (`Assoc [ ("phase", `String "setup"); ("diagnostic", diagnostic d) ]);
          exit 2
      | Ok simulator ->
          let (module S : Sim.SIM) = simulator in
          let before = S.Interface.checkpoint () in
          let boot = S.Interface.parse_program [ include_dir ] [ program ] in
          let after_boot = S.Interface.checkpoint () in
          let boot_json, result =
            match boot with
            | Run.Fail d ->
                (`Null,
                 `Assoc
                   [ ("class", `String "syntax");
                     ("diagnostic", diagnostic d) ])
            | Run.Pass value ->
                let result = S.Interp.eval_rel relation [ value ] in
                (value_json value, result_json result)
          in
          emit
            (`Assoc
              [ ("relation", `String relation);
                ("mode", `String "AL");
                ("cache", `Bool true);
                ("det", `Bool false);
                ("guard", `Bool false);
                ("counterBefore", `Int before);
                ("counterAfterBoot", `Int after_boot);
                ("counterAfter", `Int (S.Interface.checkpoint ()));
                ("boot", boot_json);
                ("result", result) ]))

let () =
  match Array.to_list Sys.argv with
  | [ _; spec_dir; include_dir; program; relation ] ->
      if relation <> "Program_ok" && relation <> "Program_inst" then
        failwith "relation must be Program_ok or Program_inst";
      run spec_dir include_dir program relation
  | _ -> failwith "usage: probe SPEC_DIR INCLUDE_DIR PROGRAM RELATION"
