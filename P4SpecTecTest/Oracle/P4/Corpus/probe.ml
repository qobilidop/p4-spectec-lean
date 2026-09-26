(* Corpus v2: independent AL sessions plus a distinct Type.Fresh sentinel. *)

module Run = Runtime.Dynamic_Runner.Signature
module Sim = Runtime.Sim.Signature

let diagnostic (d : Diagnostic.t) =
  let region, message = Diagnostic.region_msg d in
  `Assoc [ ("source", `String d.source);
    ("code", match d.code with None -> `Null | Some s -> `String s);
    ("message", `String message);
    ("region", `String (Util.Source.string_of_region region)) ]

let result_json = function
  | Run.Pass values ->
      `Assoc [ ("class", `String "pass");
        ("outputs", `List (List.map Lang.Il.value_to_yojson values)) ]
  | Run.Fail (Run.Unmatch traces) ->
      `Assoc [ ("class", `String "unmatch");
        ("diagnostic", diagnostic (Run.diagnostic_of_failure (Run.Unmatch traces))) ]
  | Run.Fail (Run.Abort d) ->
      `Assoc [ ("class", `String "abort"); ("diagnostic", diagnostic d) ]

let tick () = !(Runtime.Type.Fresh.tick)
let emit json = print_endline (Yojson.Safe.to_string json)

let run spec_dir include_dir program relation =
  let before_spec = tick () in
  match Pass.algo [ spec_dir ] with
  | Error d -> emit (`Assoc [ ("phase", `String "spec");
      ("diagnostic", diagnostic d) ]); exit 2
  | Ok spec ->
      let after_spec = tick () in
      match Backend_sim.Build.build ~cache:true ~det:false ~guard:false (Run.AL spec) with
      | Error d -> emit (`Assoc [ ("phase", `String "setup");
          ("diagnostic", diagnostic d) ]); exit 2
      | Ok simulator ->
          let after_setup = tick () in
          let (module S : Sim.SIM) = simulator in
          let before = S.Interface.checkpoint () in
          let boot = S.Interface.parse_program [ include_dir ] [ program ] in
          let after_boot = S.Interface.checkpoint () in
          let type_after_boot = tick () in
          let boot_json, result = match boot with
            | Run.Fail d -> (`Null, `Assoc [ ("class", `String "syntax");
                ("diagnostic", diagnostic d) ])
            | Run.Pass value ->
                let result = S.Interp.eval_rel relation [ value ] in
                (Lang.Il.value_to_yojson value, result_json result)
          in
          emit (`Assoc [ ("relation", `String relation); ("mode", `String "AL");
            ("cache", `Bool true); ("det", `Bool false); ("guard", `Bool false);
            ("counterBefore", `Int before); ("counterAfterBoot", `Int after_boot);
            ("counterAfter", `Int (S.Interface.checkpoint ()));
            ("typeFresh", `Assoc [ ("beforeSpec", `Int before_spec);
              ("afterSpec", `Int after_spec); ("afterSetup", `Int after_setup);
              ("afterBoot", `Int type_after_boot); ("after", `Int (tick ())) ]);
            ("boot", boot_json); ("result", result) ])

let () = match Array.to_list Sys.argv with
  | [ _; spec_dir; include_dir; program; relation ] ->
      if relation <> "Program_ok" && relation <> "Program_inst" then
        failwith "relation must be Program_ok or Program_inst";
      run spec_dir include_dir program relation
  | _ -> failwith "usage: probe SPEC_DIR INCLUDE_DIR PROGRAM RELATION"
