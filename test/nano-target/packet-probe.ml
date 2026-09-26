module Run = Runtime.Dynamic_Runner.Signature
module V = Runtime.Value

let events = ref []
let driver_events = ref []
let values vs = `List (List.map Lang.Il.value_to_yojson vs)
let packet (port, payload) = `List [`Int port; `String payload]

module Observe (Spec : Backend_sim.Spec.S) = struct
  module Recorded = struct
    include Spec
    module Rel = struct
      include Spec.Rel
      let nanoswitch_drive ctx packet =
        let inputs = values [ctx; packet] in
        let before = Interface.NanoP4.checkpoint () in
        let counters () = [("counterBefore", `Int before);
          ("counterAfter", `Int (Interface.NanoP4.checkpoint ()))] in
        try
          let ctx', decision = Spec.Rel.nanoswitch_drive ctx packet in
          events := !events @ [`Assoc (counters () @ [("inputs", inputs);
            ("class", `String "pass"); ("outputs", values [decision; ctx'])])];
          (ctx', decision)
        with Run.ExternError failure ->
          events := !events @ [`Assoc (counters () @ [("inputs", inputs);
            ("class", `String "runtimeFail")])];
          raise (Run.ExternError failure)
    end
  end
  module Original = Backend_sim.Nano_switch.Pipe.Make (Recorded)
  include Original
  let drive_pipe ctx arch rx =
    let inputs = values [ctx; arch] in
    let before = Interface.NanoP4.checkpoint () in
    let fields () = [("inputs", inputs); ("rx", packet rx);
      ("counterBefore", `Int before);
      ("counterAfter", `Int (Interface.NanoP4.checkpoint ()))] in
    try
      let ctx', arch', txs = Original.drive_pipe ctx arch rx in
      driver_events := !driver_events @ [`Assoc (fields () @
        [("class", `String "pass"); ("outputs", values [ctx'; arch']);
         ("txs", `List (List.map packet txs))])];
      (ctx', arch', txs)
    with Run.ExternError failure ->
      driver_events := !driver_events @ [`Assoc (fields () @
        [("class", `String "runtimeFail")])];
      raise (Run.ExternError failure)
end

module S = Backend_sim.Make.Make (Interface.NanoP4) (Observe)
  (Interp_al.Interp.Make) (Interp_sl.Interp.Make) (Interp_pl.Interp.Make)

let () =
  match Array.to_list Sys.argv with
  | [_; spec_dir; include_dir; program; stf; guard] ->
      let spec = match Pass.algo [spec_dir] with
        | Ok spec -> spec | Error _ -> failwith "AL compilation failed" in
      (match S.init ~cache:false ~det:false ~guard:(bool_of_string guard) (Run.AL spec) with
      | Ok () -> () | Error _ -> failwith "initialization failed");
      let result = match S.run_stf_test [include_dir] program stf with
        | Run.Pass () -> "pass"
        | Run.Fail (`Syntax _) -> "syntaxFail"
        | Run.Fail (`Runtime _) -> "runtimeFail" in
      print_endline ("OBSERVATION " ^ Yojson.Safe.to_string
        (`Assoc [("stfResult", `String result); ("events", `List !events);
          ("driverEvents", `List !driver_events)]))
  | _ -> failwith "usage: probe SPEC INCLUDE PROGRAM STF GUARD"
