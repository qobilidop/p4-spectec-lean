module Run = Runtime.Dynamic_Runner.Signature
module Sim = Runtime.Sim.Signature

(* Observe one pinned STF session of a target (v1model or eBPF): the parsed program, the
   pipeline initialization, every driven packet with the states before and after it, every
   control-plane change of the architecture, and upstream's own STF verdict. The original
   pipe code runs unchanged; the probe only records values at the architecture's
   boundaries. Table entries and default actions are applied by upstream's statement runner
   directly, so their effect is observed through the state before the next packet. *)

let value v = Lang.Il.value_to_yojson v
let packet (port, payload) = `List [`Int port; `String payload]
let counter () = ref 0
let events = ref []
let record (event : Yojson.Safe.t) = events := event :: !events

module Observe (MakeArch : functor (Spec : Backend_sim.Spec.S) -> Sim.ARCH)
    (Spec : Backend_sim.Spec.S) = struct
  module Original = MakeArch (Spec)
  include Original

  let init_pipe includes path =
    let counter_start = Interface.P4.checkpoint () in
    try
      let ctx, arch = Original.init_pipe includes path in
      record (`Assoc [("kind", `String "init"); ("class", `String "pass");
        ("counterStart", `Int counter_start); ("counterEnd", `Int (Interface.P4.checkpoint ()));
        ("ctx", value ctx); ("arch", value arch)]);
      (ctx, arch)
    with Run.ExternError failure ->
      record (`Assoc [("kind", `String "init"); ("class", `String "runtimeFail");
        ("counterStart", `Int counter_start); ("counterEnd", `Int (Interface.P4.checkpoint ()))]);
      raise (Run.ExternError failure)

  let drive_pipe ctx arch rx =
    let counter_start = Interface.P4.checkpoint () in
    let before = `Assoc [("ctx", value ctx); ("arch", value arch)] in
    try
      let ctx', arch', txs = Original.drive_pipe ctx arch rx in
      record (`Assoc [("kind", `String "packet"); ("rx", packet rx); ("class", `String "pass");
        ("counterStart", `Int counter_start); ("counterEnd", `Int (Interface.P4.checkpoint ()));
        ("before", before); ("ctx", value ctx'); ("arch", value arch');
        ("txs", `List (List.map packet txs))]);
      (ctx', arch', txs)
    with Run.ExternError failure ->
      record (`Assoc [("kind", `String "packet"); ("rx", packet rx);
        ("class", `String "runtimeFail"); ("counterStart", `Int counter_start);
        ("counterEnd", `Int (Interface.P4.checkpoint ())); ("before", before)]);
      raise (Run.ExternError failure)

  let arch_change kind f =
    try
      let arch' = f () in
      record (`Assoc [("kind", `String kind); ("class", `String "pass"); ("arch", value arch')]);
      arch'
    with Run.ExternError failure ->
      record (`Assoc [("kind", `String kind); ("class", `String "runtimeFail")]);
      raise (Run.ExternError failure)

  let add_mirror_session arch session port =
    arch_change "mirroring_add" (fun () -> Original.add_mirror_session arch session port)
  let mc_mgrp_create arch mgid = arch_change "mc_mgrp_create" (fun () -> Original.mc_mgrp_create arch mgid)
  let mc_node_create arch rid ports =
    arch_change "mc_node_create" (fun () -> Original.mc_node_create arch rid ports)
  let mc_node_associate arch mgid handle =
    arch_change "mc_node_associate" (fun () -> Original.mc_node_associate arch mgid handle)
end

module V1model = Observe (Backend_sim.V1model.Pipe.Make)
module Ebpf = Observe (Backend_sim.Ebpf.Pipe.Make)
module S_v1model = Backend_sim.Make.Make (Interface.P4) (V1model)
  (Interp_al.Interp.Make) (Interp_sl.Interp.Make) (Interp_pl.Interp.Make)
module S_ebpf = Backend_sim.Make.Make (Interface.P4) (Ebpf)
  (Interp_al.Interp.Make) (Interp_sl.Interp.Make) (Interp_pl.Interp.Make)

(* The parsed statements, as the AST variants. *)
let number n = `String n
let mtchkind = function
  | Stf.Ast.Num n -> `List [`String "Num"; number n]
  | Stf.Ast.Slash (n, m) -> `List [`String "Slash"; number n; number m]
let mtch (name, kind) = `List [`String name; mtchkind kind]
let action (name, args) =
  `List [`String name; `List (List.map (fun (id, n) -> `List [`String id; number n]) args)]
let opt f = function None -> `Null | Some x -> f x
let id_or_index = function
  | Stf.Ast.Id s -> `List [`String "Id"; `String s]
  | Stf.Ast.Index n -> `List [`String "Index"; number n]
let cond = function
  | Stf.Ast.Eq -> `List [`String "Eq"] | Stf.Ast.Ne -> `List [`String "Ne"]
  | Stf.Ast.Le -> `List [`String "Le"] | Stf.Ast.Lt -> `List [`String "Lt"]
  | Stf.Ast.Ge -> `List [`String "Ge"] | Stf.Ast.Gt -> `List [`String "Gt"]
let ctr = function
  | Stf.Ast.Bytes -> `List [`String "Bytes"] | Stf.Ast.Packets -> `List [`String "Packets"]
let stmt : Stf.Ast.stmt -> Yojson.Safe.t = function
  | Wait -> `List [`String "Wait"]
  | RemoveAll -> `List [`String "RemoveAll"]
  | Expect (port, data, exact) -> `List [`String "Expect"; `String port; opt (fun s -> `String s) data; `Bool exact]
  | Packet (port, data) -> `List [`String "Packet"; `String port; `String data]
  | NoPacket -> `List [`String "NoPacket"]
  | Add (name, priority, mtches, act, id) ->
      `List [`String "Add"; `String name; opt (fun p -> `Int p) priority;
        `List (List.map mtch mtches); action act; opt (fun s -> `String s) id]
  | SetDefault (name, act) -> `List [`String "SetDefault"; `String name; action act]
  | CheckCounter (id, index, (c, cd, n)) ->
      `List [`String "CheckCounter"; `String id; id_or_index index; `List [opt ctr c; cond cd; number n]]
  | MirroringAdd (s, p) -> `List [`String "MirroringAdd"; `String s; `String p]
  | MirroringAddMc (s, i) -> `List [`String "MirroringAddMc"; `String s; `String i]
  | MirroringGet s -> `List [`String "MirroringGet"; `String s]
  | McGroupCreate i -> `List [`String "McGroupCreate"; `String i]
  | McNodeCreate (i, ports) -> `List [`String "McNodeCreate"; `String i; `List (List.map (fun p -> `String p) ports)]
  | McNodeAssociate (i, h) -> `List [`String "McNodeAssociate"; `String i; `String h]
  | RegisterRead (n, i) -> `List [`String "RegisterRead"; `String n; `String i]
  | RegisterWrite (n, i, v) -> `List [`String "RegisterWrite"; `String n; `String i; `String v]
  | RegisterReset n -> `List [`String "RegisterReset"; `String n]

let () =
  match Array.to_list Sys.argv with
  | [_; arch; spec_dir; include_dir; program; stf] ->
      let (module S : Sim.SIM) = match arch with
        | "v1model" -> (module S_v1model)
        | "ebpf" -> (module S_ebpf)
        | _ -> failwith ("unknown target architecture: " ^ arch) in
      let spec = match Pass.algo [spec_dir] with
        | Ok spec -> spec | Error _ -> failwith "AL compilation failed" in
      (match S.init ~cache:true ~det:false ~guard:false (Run.AL spec) with
      | Ok () -> () | Error _ -> failwith "initialization failed");
      let stmts = Stf.Parse.parse_file stf in
      let counter_before = S.Interface.checkpoint () in
      (* The parsed program, as the session's replay input; parsing is pure. *)
      let boot = match S.Interface.parse_program [include_dir] [program] with
        | Run.Pass v -> value v
        | Run.Fail _ -> `Null in
      let counter_after_boot = S.Interface.checkpoint () in
      let result = match boot with
        | `Null -> "syntaxFail"
        | _ ->
            (match S.run_stf_test [include_dir] program stf with
             | Run.Pass () -> "pass"
             | Run.Fail (`Syntax _) -> "syntaxFail"
             | Run.Fail (`Runtime _) -> "runtimeFail") in
      print_endline ("OBSERVATION " ^ Yojson.Safe.to_string
        (`Assoc [("stfResult", `String result); ("boot", boot);
          ("counterBefore", `Int counter_before); ("counterAfterBoot", `Int counter_after_boot);
          ("counterAfter", `Int (S.Interface.checkpoint ()));
          ("stmts", `List (List.map stmt stmts)); ("events", `List (List.rev !events))]))
  | _ -> failwith "usage: probe ARCH SPEC INCLUDE PROGRAM STF"
