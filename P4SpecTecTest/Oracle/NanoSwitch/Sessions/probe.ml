module Run = Runtime.Dynamic_Runner.Signature

(* Observe complete pinned NanoSwitch STF sessions: target initialization, then every
   driven packet with its forwarding decision, transmissions and resulting context. The
   original pipe code runs unchanged; the probe only records values at its boundaries. *)

let init = ref `Null
let drives = ref []
let decisions = ref []
let value v = Lang.Il.value_to_yojson v
let packet (port, payload) = `List [`Int port; `String payload]

module Observe (Spec : Backend_sim.Spec.S) = struct
  module Recorded = struct
    include Spec
    module Rel = struct
      include Spec.Rel
      let nanoswitch_drive ctx state =
        let ctx', decision = Spec.Rel.nanoswitch_drive ctx state in
        decisions := !decisions @ [value decision];
        (ctx', decision)
    end
  end
  module Original = Backend_sim.Nano_switch.Pipe.Make (Recorded)
  include Original
  let init_pipe includes path =
    try
      let ctx, arch = Original.init_pipe includes path in
      init := `Assoc [("class", `String "pass"); ("ctx", value ctx); ("arch", value arch)];
      (ctx, arch)
    with Run.ExternError failure ->
      init := `Assoc [("class", `String "runtimeFail")];
      raise (Run.ExternError failure)
  let drive_pipe ctx arch rx =
    try
      let ctx', arch', txs = Original.drive_pipe ctx arch rx in
      drives := !drives @ [`Assoc [("rx", packet rx); ("class", `String "pass");
        ("ctx", value ctx'); ("arch", value arch'); ("txs", `List (List.map packet txs))]];
      (ctx', arch', txs)
    with Run.ExternError failure ->
      drives := !drives @ [`Assoc [("rx", packet rx); ("class", `String "runtimeFail")]];
      raise (Run.ExternError failure)
end

module S = Backend_sim.Make.Make (Interface.NanoP4) (Observe)
  (Interp_al.Interp.Make) (Interp_sl.Interp.Make) (Interp_pl.Interp.Make)

let () =
  match Array.to_list Sys.argv with
  | [_; spec_dir; include_dir; program; stf] ->
      let spec = match Pass.algo [spec_dir] with
        | Ok spec -> spec | Error _ -> failwith "AL compilation failed" in
      (match S.init ~cache:false ~det:false ~guard:false (Run.AL spec) with
      | Ok () -> () | Error _ -> failwith "initialization failed");
      let result = match S.run_stf_test [include_dir] program stf with
        | Run.Pass () -> "pass"
        | Run.Fail (`Syntax _) -> "syntaxFail"
        | Run.Fail (`Runtime _) -> "runtimeFail" in
      print_endline ("OBSERVATION " ^ Yojson.Safe.to_string
        (`Assoc [("stfResult", `String result); ("init", !init);
          ("drives", `List !drives); ("decisions", `List !decisions)]))
  | _ -> failwith "usage: probe SPEC INCLUDE PROGRAM STF"
