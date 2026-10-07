import P4SpecTec.Util.Yojson

/-!
Port of `p4spec/lib/stf/ast.ml`: the STF statements, and a decoder of the JSON the session
probe prints for upstream's parsed statements (a variant is a list headed by its constructor
name, an option `null` or the value). STF parsing itself stays upstream.
-/

namespace P4SpecTec.BackendSim.Stf.Ast

open Lean (Json)
open P4SpecTec.Util.Yojson

/-- Mirrors `mtchkind`: a number, or a value and a mask. -/
inductive mtchkind where
  /-- A number, as written. -/
  | Num (number : String)
  /-- A prefix and its mask length. -/
  | Slash (number mask : String)
  deriving BEq, Repr

/-- Mirrors `mtch`: a key name and how it matches. -/
abbrev mtch := String × mtchkind

/-- Mirrors `action`: an action name and its named arguments. -/
abbrev action := String × List (String × String)

/-- Mirrors `id_or_index`. -/
inductive id_or_index where
  /-- A name. -/
  | Id (id : String)
  /-- An index. -/
  | Index (number : String)
  deriving BEq, Repr

/-- Mirrors `cond`. -/
inductive cond where
  /-- `==` -/
  | Eq
  /-- `!=` -/
  | Ne
  /-- `<=` -/
  | Le
  /-- `<` -/
  | Lt
  /-- `>=` -/
  | Ge
  /-- `>` -/
  | Gt
  deriving BEq, Repr

/-- Mirrors `ctr`. -/
inductive ctr where
  /-- Bytes. -/
  | Bytes
  /-- Packets. -/
  | Packets
  deriving BEq, Repr

/-- Mirrors `stmt`. -/
inductive stmt where
  /-- `wait` -/
  | Wait
  /-- `remove_all` -/
  | RemoveAll
  /-- `expect PORT [DATA] [$]` -/
  | Expect (port : String) (data : Option String) (exact : Bool)
  /-- `packet PORT DATA` -/
  | Packet (port : String) (packet : String)
  /-- `no_packet` -/
  | NoPacket
  /-- `add TABLE [PRIORITY] MATCHES ACTION [= ID]` -/
  | Add (table : String) (priority : Option Int) (mtches : List mtch) (action : action)
      (id : Option String)
  /-- `setdefault TABLE ACTION` -/
  | SetDefault (table : String) (action : action)
  /-- `check_counter` -/
  | CheckCounter (id : String) (index : id_or_index) (ctr : Option ctr) (cond : cond)
      (number : String)
  /-- `mirroring_add SESSION PORT` -/
  | MirroringAdd (session port : String)
  /-- `mirroring_add_mc SESSION MGID` -/
  | MirroringAddMc (session id : String)
  /-- `mirroring_get SESSION` -/
  | MirroringGet (session : String)
  /-- `mc_mgrp_create MGID` -/
  | McGroupCreate (id : String)
  /-- `mc_node_create RID PORTS` -/
  | McNodeCreate (id : String) (ports : List String)
  /-- `mc_node_associate MGID HANDLE` -/
  | McNodeAssociate (id handle : String)
  /-- `register_read NAME INDEX` -/
  | RegisterRead (name index : String)
  /-- `register_write NAME INDEX VALUE` -/
  | RegisterWrite (name index value : String)
  /-- `register_reset NAME` -/
  | RegisterReset (name : String)
  deriving BEq, Repr

/-- Decode `mtchkind`. -/
def mtchkind_of : D mtchkind := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "Num", #[n] => .Num <$> str n
  | "Slash", #[n, m] => do pure (.Slash (← str n) (← str m))
  | _, _ => fail "expected mtchkind" j

/-- Decode `mtch`. -/
def mtch_of : D mtch := pair str mtchkind_of

/-- Decode `action`. -/
def action_of : D action := pair str (list (pair str str))

/-- Decode `id_or_index`. -/
def id_or_index_of : D id_or_index := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "Id", #[s] => .Id <$> str s
  | "Index", #[n] => .Index <$> str n
  | _, _ => fail "expected id_or_index" j

/-- Decode `cond`. -/
def cond_of : D cond := fun j => do
  match ← variant j with
  | ("Eq", _) => pure .Eq | ("Ne", _) => pure .Ne | ("Le", _) => pure .Le
  | ("Lt", _) => pure .Lt | ("Ge", _) => pure .Ge | ("Gt", _) => pure .Gt
  | _ => fail "expected cond" j

/-- Decode `ctr`. -/
def ctr_of : D ctr := fun j => do
  match ← variant j with
  | ("Bytes", _) => pure .Bytes
  | ("Packets", _) => pure .Packets
  | _ => fail "expected ctr" j

/-- Decode `stmt`. -/
def stmt_of : D stmt := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "Wait", #[] => pure .Wait
  | "RemoveAll", #[] => pure .RemoveAll
  | "Expect", #[p, d, e] => do pure (.Expect (← str p) (← opt str d) (← bool e))
  | "Packet", #[p, d] => do pure (.Packet (← str p) (← str d))
  | "NoPacket", #[] => pure .NoPacket
  | "Add", #[t, p, ms, act, i] => do
    pure (.Add (← str t) (← opt int p) (← list mtch_of ms) (← action_of act) (← opt str i))
  | "SetDefault", #[t, act] => do pure (.SetDefault (← str t) (← action_of act))
  | "CheckCounter", #[i, ix, .arr #[ct, cd, n]] => do
    pure (.CheckCounter (← str i) (← id_or_index_of ix) (← opt ctr_of ct) (← cond_of cd) (← str n))
  | "MirroringAdd", #[s, p] => do pure (.MirroringAdd (← str s) (← str p))
  | "MirroringAddMc", #[s, i] => do pure (.MirroringAddMc (← str s) (← str i))
  | "MirroringGet", #[s] => .MirroringGet <$> str s
  | "McGroupCreate", #[i] => .McGroupCreate <$> str i
  | "McNodeCreate", #[i, ps] => do pure (.McNodeCreate (← str i) (← list str ps))
  | "McNodeAssociate", #[i, h] => do pure (.McNodeAssociate (← str i) (← str h))
  | "RegisterRead", #[n, i] => do pure (.RegisterRead (← str n) (← str i))
  | "RegisterWrite", #[n, i, v] => do pure (.RegisterWrite (← str n) (← str i) (← str v))
  | "RegisterReset", #[n] => .RegisterReset <$> str n
  | _, _ => fail "expected stmt" j

end P4SpecTec.BackendSim.Stf.Ast
