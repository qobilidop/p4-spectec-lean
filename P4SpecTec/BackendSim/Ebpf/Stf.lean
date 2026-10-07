import P4SpecTec.BackendSim.Ebpf.Pipe
import P4SpecTec.BackendSim.Stf.Run

/-!
Port of the eBPF `transform_stf_stmt` (`backend-sim/ebpf/pipe.ml`), and the eBPF
architecture's operations for the shared statement runner (`BackendSim/Stf/Run.lean`):
packets through `drive_pipe`; the mirror and multicast interfaces are not implemented
upstream and are the hard error.
-/

namespace P4SpecTec.BackendSim.Ebpf.Stf

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude
open P4SpecTec.BackendSim P4SpecTec.BackendSim.Stf

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- Mirrors the eBPF `transform_stf_stmt`: the `pipe` control's names become `main.filt`'s,
and an action name is unqualified. Matches are not rewritten. -/
def transform_stf_stmt : Ast.stmt → Ast.stmt
  | .Add name priority mtches action entry =>
    .Add (transform_name name) priority mtches (transform_action action) entry
  | .SetDefault name action => .SetDefault (transform_name name) (transform_action action)
  | stmt => stmt
where
  /-- The table-name rewriting. -/
  transform_name (name : String) : String :=
    name |> Transform.replace_substring ["pipe_c1_"] "main.filt.c1."
      |> Transform.replace_substring ["pipe_"] "main.filt."
      |> Transform.replace_substring ["pipe"] "main.filt"
  /-- The action rewriting. -/
  transform_action (action : Ast.action) : Ast.action :=
    Transform.into_unqualified
      (action.1 |> Transform.replace_substring ["pipe_c1_"] "main.filt.c1."
        |> Transform.replace_substring ["pipe_"] "main.filt."
        |> Transform.replace_substring ["_NoAction"] "NoAction", action.2)

/-- The eBPF operations of the statement runner. -/
def arch : Run.Arch m :=
  { transform_stf_stmt, drive_pipe := Pipe.drive_pipe,
    add_mirror_session := fun _ _ _ _ => throw .err, mc_mgrp_create := fun _ _ _ => throw .err,
    mc_node_create := fun _ _ _ _ => throw .err, mc_node_associate := fun _ _ _ _ => throw .err }

/-- Mirrors `run_stf_stmt` on the eBPF architecture. -/
def run_stf_stmt (spec : Make.Spec m) (value_ctx value_arch : value) (stmt : Ast.stmt) :
    m Run.Outcome :=
  Run.run_stf_stmt arch spec value_ctx value_arch stmt

end P4SpecTec.BackendSim.Ebpf.Stf
