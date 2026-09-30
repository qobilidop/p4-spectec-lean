import NanoP4Target.Contract
import NanoP4Spec.Refinement.NanoSwitch_init
import NanoP4Spec.Refinement.NanoSwitch_drive

/-!
# NanoP4Target.Session

Packet sessions on the concrete NanoSwitch target, and their two-way composition theorem.
A session initializes the target from a program (`NanoSwitch_init`, upstream's `init_pipe`)
and drives a sequence of received packets (`drive_pipe`), threading the persistent context
and architecture state and collecting each packet's ordered transmissions. The reference
session runs the AL interpreter with the registered NanoSwitch externs; the generated session
runs the generated model with the typed extern instance. Not an upstream mirror: STF parsing
and expectation matching stay upstream; this is the semantic core of `run_stf_test`.

The composition theorem relates the two in both directions for every related program and
every packet sequence: per-packet transmissions and forward/drop outcomes are equal, final
contexts are related, the architecture state stays initial, and failure kinds agree. Nano
declares no fresh-identifier builtin, so the pure evaluation profile observes every state
the sessions have.
-/

namespace NanoP4Target

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Lang.Il
open P4SpecTec.BackendSim P4SpecTec.BackendSim.NanoSwitch

/-! ## Reference sessions -/

/-- Drive the reference target through received packets, threading context and architecture
state and collecting each packet's transmissions in order. -/
def referencePackets (call : Pipe.RelCall Eval) :
    value → value → List Runtime.Sim.Io.rx → Eval (value × value × List (List Runtime.Sim.Io.tx))
  | value_ctx, value_arch, [] => pure (value_ctx, value_arch, [])
  | value_ctx, value_arch, rx :: rxs => do
    let (value_ctx, value_arch, txs) ← Pipe.drive_pipe call value_ctx value_arch rx
    let (value_ctx, value_arch, rest) ← referencePackets call value_ctx value_arch rxs
    pure (value_ctx, value_arch, txs :: rest)

/-- A reference session: initialize from the parsed program, then drive the packets. -/
def referenceSession (call : Pipe.RelCall Eval) (value_program : value)
    (rxs : List Runtime.Sim.Io.rx) : Eval (value × value × List (List Runtime.Sim.Io.tx)) := do
  let (value_ctx, value_arch) ← Pipe.init_pipe call value_program
  referencePackets call value_ctx value_arch rxs

/-- The reference relation evaluator at `fuel`: upstream's registered `call_rel`. -/
abbrev relCall (cfg : Interp_al.Interp.Config) (g : Interp_al.Ctx.global) (fuel : Nat) :
    Pipe.RelCall Eval :=
  Interp_al.Interp.do_eval_rel fuel cfg g

/-! ## Generated sessions -/

/-- Whether a generated forwarding decision transmits. -/
def forwards : NanoP4Spec.forwardingDecision → Bool
  | .FORWARD => true
  | .DROP => false

/-- Drive one received packet through the generated model: the typed counterpart of
`drive_pipe`, with the same host-range and hexadecimal checks. -/
def drive (ctx : NanoP4Spec.evalContext) (rx : Runtime.Sim.Io.rx) :
    Eval (NanoP4Spec.evalContext × List Runtime.Sim.Io.tx) := do
  let (port_in, packet_bytes) := rx
  unless Core.Object.hostInt port_in do throw .err
  let packet_in ← Pipe.checked (Core.Object.PacketIn.init packet_bytes)
  let (decision, ctx) ← ExceptT.mk (NanoP4Spec.NanoSwitch_drive.run ctx
    ⟨Pipe.extern_to_yojson (.PacketIn packet_in)⟩)
  pure (ctx, if forwards decision then [(port_in, packet_bytes)] else [])

/-- Drive the generated model through received packets. -/
def packets : NanoP4Spec.evalContext → List Runtime.Sim.Io.rx →
    Eval (NanoP4Spec.evalContext × List (List Runtime.Sim.Io.tx))
  | ctx, [] => pure (ctx, [])
  | ctx, rx :: rxs => do
    let (ctx, txs) ← drive ctx rx
    let (ctx, rest) ← packets ctx rxs
    pure (ctx, txs :: rest)

/-- A generated session: `NanoSwitch_init` on the program, then the packets. -/
def session (program : NanoP4Spec.program) (rxs : List Runtime.Sim.Io.rx) :
    Eval (NanoP4Spec.evalContext × List (List Runtime.Sim.Io.tx)) := do
  let ctx ← ExceptT.mk (NanoP4Spec.NanoSwitch_init.run program)
  packets ctx rxs

/-! ## Composition -/

/-- Session observations agree: related final contexts, the initial architecture state, and
equal per-packet transmissions. -/
def SessionRel (a : value × value × List (List Runtime.Sim.Io.tx))
    (b : NanoP4Spec.evalContext × List (List Runtime.Sim.Io.tx)) : Prop :=
  Rel a.1 b.1 ∧ a.2.1 = Pipe.init_arch_state ∧ a.2.2 = b.2

/-- A reference decision related to a generated one forwards exactly when it does. -/
theorem isForwardRel {v : value} {d : NanoP4Spec.forwardingDecision} (h : Rel v d) :
    Pipe.is_forward v = forwards d := by
  have h' : canon v = canon (toValue d) := h
  cases d with
  | FORWARD =>
    have hit : canon' v.it = .CaseV (.Atom (Util.Source.mkPhrase (.Keyword "FORWARD"))) := by
      rw [← canon_it, h']; rfl
    obtain ⟨m, hm, hcm⟩ := canon'_eq_case hit
    obtain ⟨a, rfl, ha⟩ := canonMixfix_eq_atom hcm
    simp +decide [Pipe.is_forward, hm, Domain.Mixfix.eq_mixop, Domain.Mixfix.eq, ha, forwards]
  | DROP =>
    have hit : canon' v.it = .CaseV (.Atom (Util.Source.mkPhrase (.Keyword "DROP"))) := by
      rw [← canon_it, h']; rfl
    obtain ⟨m, hm, hcm⟩ := canon'_eq_case hit
    obtain ⟨a, rfl, ha⟩ := canonMixfix_eq_atom hcm
    simp +decide [Pipe.is_forward, hm, Domain.Mixfix.eq_mixop, Domain.Mixfix.eq, ha, forwards]

/-- One related output: the reference returns exactly one value. -/
theorem outsOne {vs : List value} {x : value} (h : Outs vs [x]) :
    ∃ a, vs = [a] ∧ canon a = canon x := by
  obtain ⟨a, rest, rfl, ha, hrest⟩ := canons_eq_cons (vs := vs) h
  cases canons_eq_nil hrest
  exact ⟨a, rfl, ha⟩

/-- Two related outputs: the reference returns exactly two values. -/
theorem outsTwo {vs : List value} {x y : value} (h : Outs vs [x, y]) :
    ∃ a b, vs = [a, b] ∧ canon a = canon x ∧ canon b = canon y := by
  obtain ⟨a, rest, rfl, ha, hrest⟩ := canons_eq_cons (vs := vs) h
  obtain ⟨b, rest, rfl, hb, hrest⟩ := canons_eq_cons hrest
  cases canons_eq_nil hrest
  exact ⟨a, b, rfl, ha, hb⟩

/-- The reference's serialized packet state is the generated object state. -/
theorem packetStateRel (json : Lean.Json) :
    Rel (Runtime.Value.Make.extern (Pipe.varT "objectState") json)
      (⟨json⟩ : NanoP4Spec.objectState) := rfl

/-- A driven packet's observations: related contexts, the architecture state passed through,
and equal transmissions. -/
def DriveRel (arch : value) (a : value × value × List Runtime.Sim.Io.tx)
    (b : NanoP4Spec.evalContext × List Runtime.Sim.Io.tx) : Prop :=
  Rel a.1 b.1 ∧ a.2.1 = arch ∧ a.2.2 = b.2

/-- Observations after a sequence of packets. -/
def PacketsRel (arch : value) (a : value × value × List (List Runtime.Sim.Io.tx))
    (b : NanoP4Spec.evalContext × List (List Runtime.Sim.Io.tx)) : Prop :=
  Rel a.1 b.1 ∧ a.2.1 = arch ∧ a.2.2 = b.2

section Composition

variable {cfg : Interp_al.Interp.Config} {g : Interp_al.Ctx.global}

/-- The hypotheses of every session theorem: the reference target configuration with the
pinned empty print hints, and a global context satisfying the specification with every
defined function's type parameter fresh (as the initialized environment provides). -/
structure SessionEnv (cfg : Interp_al.Interp.Config) (g : Interp_al.Ctx.global) : Prop where
  /-- The reference target configuration. -/
  reference : Reference cfg
  /-- The pinned Nano print-hint table is empty. -/
  hints : cfg.printHints = []
  /-- The global tables hold the specification. -/
  spec : HoldsSpec NanoP4Spec.spec g
  /-- Type parameter `X` is fresh. -/
  freshX : g.tdtbl.get? "X" = none
  /-- Type parameter `K` is fresh. -/
  freshK : g.tdtbl.get? "K" = none
  /-- Type parameter `V` is fresh. -/
  freshV : g.tdtbl.get? "V" = none

/-- Forward correspondence of one driven packet, at every fuel. -/
theorem driveRefines (henv : SessionEnv cfg g) (fuel : Nat) (arch : value)
    (rx : Runtime.Sim.Io.rx) {vctx : value} {ctx : NanoP4Spec.evalContext}
    (hctx : Rel vctx ctx) :
    Refines (DriveRel arch) (Pipe.drive_pipe (relCall cfg g fuel) vctx arch rx)
      (drive ctx rx) := by
  obtain ⟨port, bytes⟩ := rx
  unfold Pipe.drive_pipe drive
  by_cases hport : Core.Object.hostInt port = true
  · simp only [hport, ↓reduceIte]
    cases hinit : Core.Object.PacketIn.init bytes with
    | error e =>
      simp only [Pipe.checked]
      exact refines_throw
    | ok pkt =>
      simp only [Pipe.checked, pure_bind]
      refine refines_bind (NanoP4Spec.NanoSwitch_drive.refines fuel cfg (Interp_al.Ctx.empty g)
        false henv.reference.guard henv.hints (externsContractHolds henv.reference) rfl
        henv.spec henv.freshK henv.freshV henv.freshX _ _ ctx _ hctx (packetStateRel _))
        fun outs o hrel => ?_
      obtain ⟨decision, ctx'⟩ := o
      obtain ⟨vdecision, vctx', rfl, hd, hc⟩ := outsTwo hrel
      simp only
      rw [isForwardRel (show Rel vdecision decision from hd)]
      exact refines_pure ⟨hc, rfl, rfl⟩
  · simp only [hport]
    exact refines_throw

/-- Reverse correspondence of one driven packet. -/
theorem driveRealizes (henv : SessionEnv cfg g) (arch : value) (rx : Runtime.Sim.Io.rx)
    {vctx : value} {ctx : NanoP4Spec.evalContext} (hctx : Rel vctx ctx) :
    Realizes (DriveRel arch) (fun fuel => Pipe.drive_pipe (relCall cfg g fuel) vctx arch rx)
      (drive ctx rx) := by
  obtain ⟨port, bytes⟩ := rx
  unfold Pipe.drive_pipe drive
  by_cases hport : Core.Object.hostInt port = true
  · simp only [hport, ↓reduceIte]
    cases hinit : Core.Object.PacketIn.init bytes with
    | error e =>
      simp only [Pipe.checked]
      exact Realizes.error _ _
    | ok pkt =>
      simp only [Pipe.checked, pure_bind]
      refine Realizes.bind (NanoP4Spec.NanoSwitch_drive.realizes cfg (Interp_al.Ctx.empty g)
        false henv.reference.guard henv.hints (externsContractHolds henv.reference) rfl
        henv.spec henv.freshK henv.freshV henv.freshX _ _ ctx _ hctx (packetStateRel _))
        fun outs o hrel => ?_
      obtain ⟨decision, ctx'⟩ := o
      obtain ⟨vdecision, vctx', rfl, hd, hc⟩ := outsTwo hrel
      simp only
      rw [isForwardRel (show Rel vdecision decision from hd)]
      exact Realizes.pure ⟨hc, rfl, rfl⟩
  · simp only [hport]
    exact Realizes.error _ _

/-- Forward correspondence of a packet sequence, at every fuel. -/
theorem packetsRefines (henv : SessionEnv cfg g) (fuel : Nat) (arch : value) :
    ∀ (rxs : List Runtime.Sim.Io.rx) {vctx : value} {ctx : NanoP4Spec.evalContext},
      Rel vctx ctx →
      Refines (PacketsRel arch) (referencePackets (relCall cfg g fuel) vctx arch rxs)
        (packets ctx rxs)
  | [], _, _, hctx => refines_pure ⟨hctx, rfl, rfl⟩
  | rx :: rxs, _, _, hctx => by
    simp only [referencePackets, packets]
    refine refines_bind (driveRefines henv fuel arch rx hctx) fun a b hab => ?_
    obtain ⟨vctx', arch', txs⟩ := a
    obtain ⟨ctx', txs'⟩ := b
    obtain ⟨hc, rfl, rfl⟩ := hab
    refine refines_bind (packetsRefines henv fuel arch' rxs hc) fun a b hab => ?_
    obtain ⟨vctx'', arch'', rest⟩ := a
    obtain ⟨ctx'', rest'⟩ := b
    obtain ⟨hc', rfl, rfl⟩ := hab
    exact refines_pure ⟨hc', rfl, rfl⟩

/-- Reverse correspondence of a packet sequence. -/
theorem packetsRealizes (henv : SessionEnv cfg g) (arch : value) :
    ∀ (rxs : List Runtime.Sim.Io.rx) {vctx : value} {ctx : NanoP4Spec.evalContext},
      Rel vctx ctx →
      Realizes (PacketsRel arch) (fun fuel => referencePackets (relCall cfg g fuel) vctx arch rxs)
        (packets ctx rxs)
  | [], _, _, hctx => Realizes.pure ⟨hctx, rfl, rfl⟩
  | rx :: rxs, _, _, hctx => by
    simp only [referencePackets, packets]
    refine Realizes.bind (driveRealizes henv arch rx hctx) fun a b hab => ?_
    obtain ⟨vctx', arch', txs⟩ := a
    obtain ⟨ctx', txs'⟩ := b
    obtain ⟨hc, rfl, rfl⟩ := hab
    refine Realizes.bind (packetsRealizes henv arch' rxs hc) fun a b hab => ?_
    obtain ⟨vctx'', arch'', rest⟩ := a
    obtain ⟨ctx'', rest'⟩ := b
    obtain ⟨hc', rfl, rfl⟩ := hab
    exact Realizes.pure ⟨hc', rfl, rfl⟩

/-- Forward composition of a whole session at every fuel: initialization from the program,
then every packet. -/
theorem sessionRefines (henv : SessionEnv cfg g) (fuel : Nat) {vprogram : value}
    {program : NanoP4Spec.program} (hprogram : Rel vprogram program)
    (rxs : List Runtime.Sim.Io.rx) :
    Refines SessionRel (referenceSession (relCall cfg g fuel) vprogram rxs)
      (session program rxs) := by
  unfold referenceSession session Pipe.init_pipe
  simp only [bind_assoc]
  refine refines_bind (NanoP4Spec.NanoSwitch_init.refines fuel cfg (Interp_al.Ctx.empty g)
    false henv.reference.guard henv.hints rfl henv.spec henv.freshK henv.freshV henv.freshX
    _ _ hprogram) fun outs ctx hrel => ?_
  obtain ⟨vctx, rfl, hc⟩ := outsOne hrel
  simp only [pure_bind]
  exact packetsRefines henv fuel _ rxs hc

/-- Reverse composition of a whole session. -/
theorem sessionRealizes (henv : SessionEnv cfg g) {vprogram : value}
    {program : NanoP4Spec.program} (hprogram : Rel vprogram program)
    (rxs : List Runtime.Sim.Io.rx) :
    Realizes SessionRel (fun fuel => referenceSession (relCall cfg g fuel) vprogram rxs)
      (session program rxs) := by
  unfold referenceSession session Pipe.init_pipe
  simp only [bind_assoc]
  refine Realizes.bind (NanoP4Spec.NanoSwitch_init.realizes cfg (Interp_al.Ctx.empty g)
    false henv.reference.guard henv.hints rfl henv.spec henv.freshK henv.freshV henv.freshX
    _ _ hprogram) fun outs ctx hrel => ?_
  obtain ⟨vctx, rfl, hc⟩ := outsOne hrel
  simp only [pure_bind]
  exact packetsRealizes henv _ rxs hc

/-- Two-way composition of NanoSwitch sessions: from semantic initialization of a related
program through every packet, each terminating reference session has a related generated one
at every fuel, and each terminating generated session has an eventual reference witness. -/
theorem sessionCorrespondence (henv : SessionEnv cfg g) {vprogram : value}
    {program : NanoP4Spec.program} (hprogram : Rel vprogram program)
    (rxs : List Runtime.Sim.Io.rx) :
    (∀ fuel, Refines SessionRel (referenceSession (relCall cfg g fuel) vprogram rxs)
      (session program rxs)) ∧
    Realizes SessionRel (fun fuel => referenceSession (relCall cfg g fuel) vprogram rxs)
      (session program rxs) :=
  ⟨fun fuel => sessionRefines henv fuel hprogram rxs, sessionRealizes henv hprogram rxs⟩

end Composition

/-- The concrete initialized environment of the pinned specification satisfies the session
hypotheses for every reference target configuration with the pinned empty print hints. -/
theorem initializedSessionEnv {cfg : Interp_al.Interp.Config} (hcfg : Reference cfg)
    (hhints : cfg.printHints = []) : SessionEnv cfg NanoP4Spec.Environment.global := by
  obtain ⟨_, hspec, _, hX, hK, _, hV⟩ := NanoP4Spec.Environment.initialized
  exact ⟨hcfg, hhints, hspec, hX, hK, hV⟩

/-- Session composition on the concrete initialized environment, the global tables that
`Interp_al.Ctx.init NanoP4Spec.spec` produces (`NanoP4Spec.Environment.initEqOk`). -/
theorem initializedSessionCorrespondence {cfg : Interp_al.Interp.Config} (hcfg : Reference cfg)
    (hhints : cfg.printHints = []) {vprogram : value} {program : NanoP4Spec.program}
    (hprogram : Rel vprogram program) (rxs : List Runtime.Sim.Io.rx) :
    (∀ fuel, Refines SessionRel
      (referenceSession (relCall cfg NanoP4Spec.Environment.global fuel) vprogram rxs)
      (session program rxs)) ∧
    Realizes SessionRel
      (fun fuel => referenceSession (relCall cfg NanoP4Spec.Environment.global fuel) vprogram rxs)
      (session program rxs) :=
  sessionCorrespondence (initializedSessionEnv hcfg hhints) hprogram rxs

/-- The session observations on the concrete initialized environment, with the observation
relation spelled out: related final contexts, the initial architecture state, and equal
ordered transmissions (and so forward/drop) for every packet, with failure kinds preserved. -/
theorem sessionObservations {cfg : Interp_al.Interp.Config} (hcfg : Reference cfg)
    (hhints : cfg.printHints = []) {vprogram : value} {program : NanoP4Spec.program}
    (hprogram : Rel vprogram program) (rxs : List Runtime.Sim.Io.rx) :
    (∀ fuel, Refines (fun a b => Rel a.1 b.1 ∧ a.2.1 = Pipe.init_arch_state ∧ a.2.2 = b.2)
      (referenceSession (relCall cfg NanoP4Spec.Environment.global fuel) vprogram rxs)
      (session program rxs)) ∧
    Realizes (fun a b => Rel a.1 b.1 ∧ a.2.1 = Pipe.init_arch_state ∧ a.2.2 = b.2)
      (fun fuel => referenceSession (relCall cfg NanoP4Spec.Environment.global fuel) vprogram rxs)
      (session program rxs) :=
  initializedSessionCorrespondence hcfg hhints hprogram rxs

/-! ## Transmissions -/

/-- The generated session on `program` receives `rxs` and transmits `txs`, packet by packet,
ending in some context. -/
def Transmits (program : NanoP4Spec.program) (rxs : List Runtime.Sim.Io.rx)
    (txs : List (List Runtime.Sim.Io.tx)) : Prop :=
  ∃ ctx, (session program rxs).run = some (.ok (ctx, txs))

/-- The reference session on the program value `vprogram`, in the initialized environment of
the pinned specification, transmits `txs`: it does so at every sufficiently large fuel, and
every terminating run at any fuel does so, with the initial architecture state. -/
def ReferenceTransmits (cfg : Interp_al.Interp.Config) (vprogram : value)
    (rxs : List Runtime.Sim.Io.rx) (txs : List (List Runtime.Sim.Io.tx)) : Prop :=
  (∃ bound, ∀ fuel, bound ≤ fuel → ∃ vctx,
    (referenceSession (relCall cfg NanoP4Spec.Environment.global fuel) vprogram rxs).run =
      some (.ok (vctx, Pipe.init_arch_state, txs))) ∧
  ∀ fuel r, (referenceSession (relCall cfg NanoP4Spec.Environment.global fuel) vprogram rxs).run =
      some r → ∃ vctx, r = .ok (vctx, Pipe.init_arch_state, txs)

/-- A generated transmission is the reference transmission, for every reference target
configuration with the pinned empty print hints and every program value related to the
program: by `initializedSessionCorrespondence`, in both directions. -/
theorem referenceTransmits {cfg : Interp_al.Interp.Config} (hcfg : Reference cfg)
    (hhints : cfg.printHints = []) {vprogram : value} {program : NanoP4Spec.program}
    (hprogram : Rel vprogram program) {rxs : List Runtime.Sim.Io.rx}
    {txs : List (List Runtime.Sim.Io.tx)} (h : Transmits program rxs txs) :
    ReferenceTransmits cfg vprogram rxs txs := by
  obtain ⟨ctx, hrun⟩ := h
  obtain ⟨hforward, hreverse⟩ := initializedSessionCorrespondence hcfg hhints hprogram rxs
  refine ⟨?_, fun fuel r hr => ?_⟩
  · obtain ⟨r, ⟨bound, hbound⟩, hrel⟩ := hreverse _ hrun
    refine ⟨bound, fun fuel hfuel => ?_⟩
    match r, hrel with
    | .ok (vctx, arch, txs'), ⟨_, harch, htxs⟩ =>
      subst harch; subst htxs
      exact ⟨vctx, hbound fuel hfuel⟩
  · obtain ⟨r', hr', hrel⟩ := hforward fuel r hr
    rw [hrun] at hr'
    cases hr'
    match r, hrel with
    | .ok (vctx, arch, txs'), ⟨_, harch, htxs⟩ =>
      subst harch; subst htxs
      exact ⟨vctx, rfl⟩

/-- info: 'NanoP4Target.referenceTransmits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceTransmits

/-- info: 'NanoP4Target.sessionObservations' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sessionObservations

/-- info: 'NanoP4Target.sessionCorrespondence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sessionCorrespondence

/-- info: 'NanoP4Target.initializedSessionCorrespondence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initializedSessionCorrespondence

end NanoP4Target
