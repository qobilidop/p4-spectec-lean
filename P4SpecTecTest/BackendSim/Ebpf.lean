import P4SpecTec.BackendSim.Ebpf.Stf

/-!
Unit checks of the eBPF port's host-side pieces, against values computed by hand from the
upstream OCaml: the STF name transformations and the counter array's JSON round trip.
Agreement of the pipeline itself with upstream is the session replay's obligation.
-/

namespace P4SpecTecTest.Ebpf

open P4SpecTec P4SpecTec.BackendSim

#guard Stf.Transform.replace_substring ["pipe_c1_"] "main.filt.c1." "pipe_c1_t" == "main.filt.c1.t"
#guard Stf.Transform.replace_substring ["pipe_"] "main.filt." "Pipe_t" == "main.filt.t"
#guard Stf.Transform.replace_substring ["pipe"] "main.filt" "t" == "t"
-- Each substring replaces its first occurrence, in turn.
#guard Stf.Transform.replace_substring ["a", "b"] "x" "cabab" == "cxxab"
#guard Stf.Transform.into_unqualified ("a.b.c", [("p", "1")]) == ("c", [("p", "1")])
#guard Stf.Transform.into_unqualified ("c", []) == ("c", [])

#guard Ebpf.Stf.transform_stf_stmt (.Add "pipe_c1_t" none [("h.$valid$", .Num "1")]
  ("pipe_c1_a", [("p", "1")]) none) ==
  .Add "main.filt.c1.t" none [("h.$valid$", .Num "1")] ("a", [("p", "1")]) none
#guard Ebpf.Stf.transform_stf_stmt (.SetDefault "pipe_t" ("pipe__NoAction", [])) ==
  .SetDefault "main.filt.t" ("NoAction", [])
#guard Ebpf.Stf.transform_stf_stmt (.SetDefault "pipe" ("pipe.a", [])) ==
  .SetDefault "main.filt" ("a", [])
#guard Ebpf.Stf.transform_stf_stmt (.Packet "0" "ab") == .Packet "0" "ab"

#guard match Ebpf.Object.CounterArray.of_yojson (Ebpf.Object.CounterArray.to_yojson [1, 2]) with
  | .ok counts => counts == [1, 2]
  | .error _ => false
#guard match Ebpf.Object.CounterArray.of_yojson (Lean.Json.arr #[Lean.Json.str "1"]) with
  | .ok _ => false
  | .error _ => true

/-! ## Statement runner on a trampoline-free statement -/

open P4SpecTec.Prelude P4SpecTec.Runtime P4SpecTec.Lang.Il in
section

private abbrev M := ExceptT Fail Id

private def noSpec : Make.Spec M :=
  { func := fun _ _ _ => throw .err, rel := fun _ _ => throw .err }

private def ctx : value := Value.Make.text (ByteText.ofString "ctx")

#guard match (Ebpf.Stf.run_stf_stmt noSpec ctx Ebpf.Pipe.init_arch_state .Wait).run with
  | .ok (c, a, txs) => Value.eq c ctx && Value.eq a Ebpf.Pipe.init_arch_state && txs.isEmpty
  | .error _ => false
-- The mirror interface is unimplemented upstream: the hard error, before any trampoline.
#guard match (Ebpf.Stf.run_stf_stmt noSpec ctx Ebpf.Pipe.init_arch_state
    (.MirroringAdd "1" "2")).run with
  | .error .err => true
  | _ => false
#guard match (Ebpf.Stf.run_stf_stmt noSpec ctx Ebpf.Pipe.init_arch_state .NoPacket).run with
  | .error .err => true
  | _ => false

end

end P4SpecTecTest.Ebpf
