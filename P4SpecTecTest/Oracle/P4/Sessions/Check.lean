import P4SpecTec.BackendSim.Ebpf.Stf
import P4SpecTec.BackendSim.V1Model.Stf
import P4SpecTec.Lang.Il.Json
import P4SpecTec.Lang.Il.Encode

/-!
Not a mirror. The replay of one observed STF session of a target on one Lean leg: the session
probe's record (the parsed program, the statements, and upstream's events at the
architecture's boundaries: initialization, every packet with the states before and after
it, every control-plane change) is walked statement by statement with the ported STF
runner, and each event is compared with the leg's outcome: class, context, architecture,
transmissions and fresh-identifier counter. A statement without an event (a table entry,
a default action, an expectation) is checked through the state before the next packet.

Values are compared as the corpus comparison compares them (`Runtime.Value.eq`), after the
target's serialized state is canonicalized: the IL values a register or a scheduled packet
keeps inside an extern payload lose their notes and regions, as they would outside one,
so that upstream's cache identities and source regions do not count as semantics.
-/

namespace P4SpecTecTest.Diff.P4Sessions

open Lean (Json)
open P4SpecTec P4SpecTec.Prelude P4SpecTec.Lang.Il P4SpecTec.Runtime
open P4SpecTec.BackendSim

/-- Canonicalize JSON inside an extern payload: an object of the IL value shape keeps
only its canonicalized payload. -/
partial def canonPayload (j : Json) : Json :=
  match j with
  | .obj kvs =>
    let pairs := kvs.toArray.toList
    let keys := pairs.map (·.1)
    if keys.length == 3 && keys.contains "it" && keys.contains "note" && keys.contains "at" then
      Json.mkObj [("it", canonPayload ((pairs.find? (·.1 == "it")).map (·.2) |>.getD .null))]
    else Json.mkObj (pairs.map fun (k, v) => (k, canonPayload v))
  | .arr xs => .arr (xs.map canonPayload)
  | j => j

/-- Canonicalize the extern payloads of a value, everywhere in it. -/
partial def canonValue (v : value) : value :=
  let it : value' := match v.it with
    | .ExternV json => .ExternV (canonPayload json)
    | .StructV fields => .StructV (fields.map fun (a, x) => (a, canonValue x))
    | .CaseV m => .CaseV (Domain.Mixfix.map canonValue m)
    | .TupleV vs => .TupleV (vs.map canonValue)
    | .OptV o => .OptV (o.map canonValue)
    | .ListV vs => .ListV (vs.map canonValue)
    | x => x
  { v with it }

/-- Semantic equality of two values of the target: upstream's comparison, with the
target's serialized state canonicalized. -/
def eqState (a b : value) : Bool := Value.eq (canonValue a) (canonValue b)

/-- A target's pipeline initializer and statement runner, over a leg's trampolines. -/
structure Target where
  /-- The initializer on the parsed program value. -/
  init_pipe : SpecImpl.Rel.RelCall StateEval → value → StateEval (value × value)
  /-- The statement runner, after the target's statement transformation. -/
  run_stf_stmt : Make.Spec StateEval → value → value → Stf.Ast.stmt → StateEval Stf.Run.Outcome

/-- The v1model target. -/
def v1modelTarget : Target :=
  { init_pipe := V1Model.Pipe.init_pipe, run_stf_stmt := V1Model.Stf.run_stf_stmt }

/-- The eBPF target. -/
def ebpfTarget : Target :=
  { init_pipe := Ebpf.Pipe.init_pipe, run_stf_stmt := Ebpf.Stf.run_stf_stmt }

/-- The targets by upstream's architecture name. -/
def targets : List (String × Target) := [("v1model", v1modelTarget), ("ebpf", ebpfTarget)]

/-- One Lean leg: the trampolines of the ported target over that leg's semantics, and
a check that the parsed program is within the leg's input domain. -/
structure Leg where
  /-- The trampolines. -/
  spec : Make.Spec StateEval
  /-- `none` when the program is representable, else why not. -/
  representable : value → Option String

/-- An upstream event at the architecture's boundary. -/
structure Event where
  /-- `init`, `packet`, or a control-plane change. -/
  kind : String
  /-- `pass` or `runtimeFail`. -/
  cls : String
  /-- The counter when the operation started; absent for a control-plane change, which
  evaluates nothing. -/
  counterStart : Option Int
  /-- The counter when it ended, whichever way; absent as above. -/
  counterEnd : Option Int
  /-- The context and architecture before a packet. -/
  before : Option (value × value)
  /-- The context after a passing operation (packets and initialization). -/
  ctx : Option value
  /-- The architecture after a passing operation. -/
  arch : Option value
  /-- A packet's transmissions. -/
  txs : Option (List Runtime.Sim.Io.tx)
  /-- A packet's input. -/
  rx : Option Runtime.Sim.Io.rx

private def field := Util.Yojson.field
private def str (j : Json) (key : String) : Except String String := do (← field j key).getStr?
private def counter (j : Json) (key : String) : Except String Int := do
  Util.Yojson.int (← field j key)

private def packetOf (j : Json) : Except String Runtime.Sim.Io.rx := do
  let #[port, payload] ← j.getArr? | throw "malformed packet"
  pure (← port.getInt?, ByteText.ofString (← payload.getStr?))

private def optional {α : Type} (j : Json) (key : String) (decode : Json → Except String α) :
    Except String (Option α) :=
  match j.getObjVal? key with
  | .ok v => some <$> decode v
  | .error _ => pure none

private def stateOf (b : Json) : Except String (value × value) := do
  let ctx ← Json.value (← field b "ctx")
  let arch ← Json.value (← field b "arch")
  pure (ctx, arch)

private def packetsOf (t : Json) : Except String (List Runtime.Sim.Io.tx) := do
  let items ← t.getArr?
  items.toList.mapM packetOf

/-- Decode an event. -/
def eventOf (j : Json) : Except String Event := do
  let kind ← str j "kind"
  let cls ← str j "class"
  let counterStart ← optional j "counterStart" Util.Yojson.int
  let counterEnd ← optional j "counterEnd" Util.Yojson.int
  let before ← optional j "before" stateOf
  let ctx ← optional j "ctx" Json.value
  let arch ← optional j "arch" Json.value
  let txs ← optional j "txs" packetsOf
  let rx ← optional j "rx" packetOf
  pure { kind, cls, counterStart, counterEnd, before, ctx, arch, txs, rx }

/-- The event kind a statement produces upstream, if any. -/
def eventKind : Stf.Ast.stmt → Option String
  | .Packet _ _ => some "packet"
  | .MirroringAdd _ _ => some "mirroring_add"
  | .McGroupCreate _ => some "mc_mgrp_create"
  | .McNodeCreate _ _ => some "mc_node_create"
  | .McNodeAssociate _ _ => some "mc_node_associate"
  | _ => none

/-- A session's observation. -/
structure Observation where
  /-- `pass`, `runtimeFail` or `syntaxFail`. -/
  stfResult : String
  /-- The parsed program, or `null` when parsing failed. -/
  boot : Json
  /-- The counter before and after the probe's own parse. -/
  counterBefore : Int
  /-- After the probe's parse. -/
  counterAfterBoot : Int
  /-- The statements, as parsed. -/
  stmts : List Stf.Ast.stmt
  /-- The events, in order. -/
  events : List Event

/-- Decode an observation. -/
def observationOf (j : Json) : Except String Observation := do
  pure { stfResult := ← str j "stfResult", boot := ← field j "boot",
         counterBefore := ← counter j "counterBefore",
         counterAfterBoot := ← counter j "counterAfterBoot",
         stmts := ← Util.Yojson.list Stf.Ast.stmt_of (← field j "stmts"),
         events := ← Util.Yojson.list eventOf (← field j "events") }

/-- A leg's verdict on a session. -/
structure Verdict where
  /-- The status. -/
  status : String
  /-- Where and why, for a disagreement. -/
  message : String

/-- The replay state of a leg: its context, architecture and counter. -/
structure Replay where
  /-- The context. -/
  ctx : value
  /-- The architecture. -/
  arch : value
  /-- The fresh-identifier state. -/
  fresh : FreshState

/-- Run a carrier computation from a state; `none` is exhaustion. -/
def step {α : Type} (fresh : FreshState) (x : StateEval α) :
    Except Verdict (Except Fail α × FreshState) :=
  match StateEval.run x fresh with
  | none => .error ⟨"exhausted", "the leg did not terminate within its bound"⟩
  | some r => .ok r

/-- Check a passing event against the leg's outcome. -/
def checkAfter (where_ : String) (event : Event) (ctx arch : value) (fresh : FreshState) :
    Except Verdict Unit := do
  if let some after := event.counterEnd then
    if fresh.counter != after then
      throw ⟨"counter-disagreement", s!"{where_}: Lean {fresh.counter}, upstream {after}"⟩
  match event.ctx, event.arch with
  | some c, some a =>
    unless eqState ctx c do throw ⟨"state-disagreement", s!"{where_}: context differs"⟩
    unless eqState arch a do throw ⟨"state-disagreement", s!"{where_}: architecture differs"⟩
  | none, some a =>
    -- A control-plane change records the architecture alone; the context is untouched.
    if event.kind == "init" || event.kind == "packet" then
      throw ⟨"invalid-artifact", s!"{where_}: passing event without context"⟩
    unless eqState arch a do throw ⟨"state-disagreement", s!"{where_}: architecture differs"⟩
  | _, _ => throw ⟨"invalid-artifact", s!"{where_}: passing event without state"⟩

/-- Replay one leg over the session, on a target. -/
def replay (target : Target) (leg : Leg) (obs : Observation) : Except Verdict Unit := do
  if obs.stfResult != "pass" then throw ⟨"upstream-" ++ obs.stfResult, "not evaluated"⟩
  let boot ← match Json.value obs.boot with
    | .ok v => pure v
    | .error e => throw ⟨"invalid-artifact", s!"program: {e}"⟩
  if let some why := leg.representable boot then throw ⟨"unrepresentable-input", why⟩
  let parse := obs.counterAfterBoot - obs.counterBefore
  let (init :: events) := obs.events | throw ⟨"invalid-artifact", "no initialization event"⟩
  unless init.kind == "init" do throw ⟨"invalid-artifact", "first event is not initialization"⟩
  let some start := init.counterStart | throw ⟨"invalid-artifact", "initialization without counter"⟩
  let fresh := FreshState.ofInt (start + parse)
  let (outcome, fresh) ← step fresh (target.init_pipe leg.spec.rel boot)
  let (ctx, arch) ← match outcome, init.cls with
    | .ok (ctx, arch), "pass" => pure (ctx, arch)
    | .error _, "runtimeFail" => throw ⟨"matched", "initialization fails as upstream's does"⟩
    | .ok _, _ => throw ⟨"outcome-disagreement", "initialization passes, upstream's failed"⟩
    | .error _, _ => throw ⟨"outcome-disagreement", "initialization fails, upstream's passed"⟩
  checkAfter "initialization" init ctx arch fresh
  let mut state : Replay := { ctx, arch, fresh }
  let mut events := events
  let mut index := 0
  for stmt in obs.stmts do
    index := index + 1
    let where_ := s!"statement {index}"
    let event ← match eventKind stmt with
      | none => pure none
      | some kind =>
        let (event :: rest) := events
          | throw ⟨"invalid-artifact", s!"{where_}: no upstream event for {kind}"⟩
        unless event.kind == kind do
          throw ⟨"invalid-artifact", s!"{where_}: upstream event {event.kind}, expected {kind}"⟩
        events := rest
        pure (some event)
    if let some event := event then
      if let some start := event.counterStart then
        if start != state.fresh.counter then
          throw ⟨"counter-disagreement",
            s!"{where_}: Lean starts at {state.fresh.counter}, upstream at {start}"⟩
      if let some (c, a) := event.before then
        unless eqState state.ctx c do throw ⟨"state-disagreement", s!"{where_}: context before"⟩
        unless eqState state.arch a do
          throw ⟨"state-disagreement", s!"{where_}: architecture before"⟩
    let (outcome, fresh) ←
      step state.fresh (target.run_stf_stmt leg.spec state.ctx state.arch stmt)
    match outcome, event with
    | .ok (ctx, arch, txs), some event =>
      unless event.cls == "pass" do
        throw ⟨"outcome-disagreement", s!"{where_}: passes, upstream's failed"⟩
      if let some expected := event.txs then
        unless txs == expected do throw ⟨"packet-disagreement", s!"{where_}: transmissions"⟩
      checkAfter where_ event ctx arch fresh
      state := { ctx, arch, fresh }
    | .ok (ctx, arch, _), none => state := { ctx, arch, fresh }
    | .error _, some event =>
      if event.cls == "runtimeFail" then
        if let some after := event.counterEnd then
          if fresh.counter != after then
            throw ⟨"counter-disagreement",
              s!"{where_}: fails at {fresh.counter}, upstream at {after}"⟩
        throw ⟨"matched", s!"{where_}: fails as upstream's does"⟩
      throw ⟨"outcome-disagreement", s!"{where_}: fails, upstream's passed"⟩
    | .error _, none => throw ⟨"outcome-disagreement", s!"{where_}: fails, upstream passed"⟩
  unless events.isEmpty do throw ⟨"invalid-artifact", "upstream events without statements"⟩

/-- The verdict of a leg on a session, on a target. -/
def verdict (target : Target) (leg : Leg) (obs : Observation) : Verdict :=
  match replay target leg obs with
  | .ok () => ⟨"matched", ""⟩
  | .error v => v

/-- The verdict as JSON. -/
def Verdict.toJson (v : Verdict) : Json :=
  Json.mkObj [("status", .str v.status), ("message", .str v.message)]

end P4SpecTecTest.Diff.P4Sessions
