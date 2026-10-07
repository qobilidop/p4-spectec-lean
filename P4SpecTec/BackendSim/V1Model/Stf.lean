import P4SpecTec.BackendSim.V1Model.Pipe
import P4SpecTec.BackendSim.Stf.Run

/-!
Port of the v1model `transform_stf_stmt` (`backend-sim/v1model/pipe.ml`), and the v1model
architecture's operations for the shared statement runner (`BackendSim/Stf/Run.lean`,
upstream's `run_stf_stmt` of `make.ml`): packets through `drive_pipe`, mirror sessions and
multicast groups through the architecture.
-/

namespace P4SpecTec.BackendSim.V1Model.Stf

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude
open P4SpecTec.BackendSim P4SpecTec.BackendSim.Stf

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- Mirrors the v1model `transform_stf_stmt`: ingress and egress control names are
rewritten to `main.ig` and `main.eg`, `$valid$` keys to `isValid()`. -/
def transform_stf_stmt : Ast.stmt → Ast.stmt
  | .Add name priority mtches action entry =>
    .Add (transform_name name) priority (mtches.map Transform.rewrite_valid)
      (transform_name action.1, action.2) entry
  | .SetDefault name action => .SetDefault (transform_name name) (transform_name action.1, action.2)
  | stmt => stmt
where
  /-- The control-name rewriting. -/
  transform_name (name : String) : String :=
    Transform.rewrite_substring ["egress", "postqos", "c3"] "main.eg"
      (Transform.rewrite_substring ["ingress", "preqos"] "main.ig" name)

/-- The v1model operations of the statement runner. -/
def arch : Run.Arch m :=
  { transform_stf_stmt, drive_pipe := Pipe.drive_pipe,
    add_mirror_session := Pipe.add_mirror_session, mc_mgrp_create := Pipe.mc_mgrp_create,
    mc_node_create := Pipe.mc_node_create, mc_node_associate := Pipe.mc_node_associate }

/-- Mirrors `run_stf_stmt` on the v1model architecture. -/
def run_stf_stmt (spec : Make.Spec m) (value_ctx value_arch : value) (stmt : Ast.stmt) :
    m Run.Outcome :=
  Run.run_stf_stmt arch spec value_ctx value_arch stmt

end P4SpecTec.BackendSim.V1Model.Stf
