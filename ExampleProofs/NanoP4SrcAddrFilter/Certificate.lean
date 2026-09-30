import ExampleProofs.NanoP4SrcAddrFilter.Evaluation

/-!
# Checked source-address filter certificate

`certificate` packages the whole-program property of the pinned Nano-P4 program
`positive/src-addr-filter.p4` as proof obligations, not strings naming theorems. Its parser
extracts the Nanonet header (`drop`, `packetType`, `src`, `dst`); its table admits source
addresses 1 and 2, denies 3 and otherwise runs no action; the switch forwards the received
packet unchanged exactly when the table admitted it.

The stated input domain is every host-range port with every three-byte packet (the whole header,
each field arbitrary) and every packet shorter than the header, as the STF driver receives it in
uppercase hexadecimal. The certificate proves the exact transmissions of the generated model
with the concrete NanoSwitch target, from the quoted export through initialization, extract and
the table, and transfers them to the reference AL interpreter with the registered NanoSwitch
externs for every related program value (`referenceFilter`). Packets are unmodified upstream, so
forwarding transmits the received bytes on the received port.

The sole assumption is `PacketStateText`: Lean's `partial` JSON printer and parser round-trip
the driver's packet state. `check-consumer` separately checks that the quoted program is the
decoded export and that the STF session's proven trace (the context after initialization and
after every packet, and the transmissions) equals the pinned upstream simulator's recording.
The receiver that extract returns is discarded when the parser returns, since `packet_in` is
only copied in, so no output or state here observes it; the extern contract
(`NanoP4Target.externsContractHolds`) relates it at every call, and a colocated mutation shows a
corrupted receiver is rejected there while this certificate's claims still prove.

Packets are uppercase hexadecimal texts (`hexText`), as the pinned STF files write them; other
spellings of the same bytes are outside the family. Not certified: packets longer than the
header (a payload), STF commands other than packets, and the upstream P4 frontend that
produced the export.
-/

namespace ExampleProofs.NanoP4SrcAddrFilter

open P4SpecTec P4SpecTec.BackendSim P4SpecTec.Prelude P4SpecTec.Refine NanoP4Target

/-- The transmissions of one three-byte packet: forwarded unchanged on its port exactly when
its source address is 1 or 2, otherwise dropped. -/
def filtered (port : Int) (b0 s d : UInt8) : List (List Runtime.Sim.Io.tx) :=
  if s.toNat = 1 ∨ s.toNat = 2 then [[(port, hexText [b0, s, d])]] else [[]]

/-- The generated model filters every three-byte packet on every host port. -/
theorem filterGenerated (h : PacketStateText) (port : Int) (hport : Core.Object.hostInt port = true)
    (b0 s d : UInt8) : Transmits program [(port, hexText [b0, s, d])] (filtered port b0 s d) := by
  unfold filtered
  by_cases h1 : s.toNat = 1
  · obtain rfl : s = 1 := UInt8.toNat.inj h1
    simpa using forwardOne h port hport b0 d
  by_cases h2 : s.toNat = 2
  · obtain rfl : s = 2 := UInt8.toNat.inj h2
    simpa using forwardTwo h port hport b0 d
  have hn : ¬(s.toNat = 1 ∨ s.toNat = 2) := by omega
  simp only [hn, ↓reduceIte]
  by_cases h3 : s.toNat = 3
  · obtain rfl : s = 3 := UInt8.toNat.inj h3
    exact denyThree h port hport b0 d
  exact dropUnlisted h port hport b0 s d h1 h2 h3

/-- The generated model drops every packet shorter than the Nanonet header. -/
theorem shortGenerated (h : PacketStateText) (port : Int) (hport : Core.Object.hostInt port = true)
    (bs : List UInt8) (hshort : bs.length < 3) : Transmits program [(port, hexText bs)] [[]] := by
  match bs, hshort with
  | [], _ => exact dropEmpty h port hport
  | [b0], _ => exact dropOneByte h port hport b0
  | [b0, b1], _ => exact dropTwoBytes h port hport b0 b1
  | _ :: _ :: _ :: _, hshort => simp at hshort; omega

/-- Obligations certified for the source-address filter. Each field is a proposition over the
quoted program, the generated model, the concrete target or the reference interpreter. -/
structure Certificate : Prop where
  /-- Actual initialization of the program succeeds: it types, loads and yields a context. -/
  initialized : ∃ ctx, NanoP4Spec.NanoSwitch_init.run program = some (.ok ctx)
  /-- Every three-byte packet on every host port is forwarded unchanged exactly when its
  source address is 1 or 2, and dropped otherwise, by the generated model. -/
  filter : ∀ port, Core.Object.hostInt port = true → ∀ b0 s d : UInt8,
    Transmits program [(port, hexText [b0, s, d])] (filtered port b0 s d)
  /-- Every packet shorter than the Nanonet header is dropped. -/
  short : ∀ port, Core.Object.hostInt port = true → ∀ bs : List UInt8, bs.length < 3 →
    Transmits program [(port, hexText bs)] [[]]
  /-- The pinned STF session's trace (the outcome after initialization and after each packet)
  is `stfTrace`; the session forwards `000100` and drops `000300` and `000A00`, threading the
  context through the three packets. -/
  stf : stfPrefixes program = stfTrace ∧
    Transmits program stfPackets [[(0, hexText [0, 1, 0])], [], []]
  /-- Every generated transmission is the reference interpreter's, at every sufficiently large
  fuel and at every terminating fuel, for every reference target configuration with the
  pinned empty print hints and every program value related to the quoted program. -/
  reference : ∀ {cfg : Interp_al.Interp.Config}, Reference cfg → cfg.printHints = [] →
    ∀ {vprogram : Lang.Il.value}, Rel vprogram program →
    ∀ rxs txs, Transmits program rxs txs → ReferenceTransmits cfg vprogram rxs txs

/-- The checked certificate, under the packet-state text premise alone. -/
theorem certificate (h : PacketStateText) : Certificate where
  initialized := ⟨_, initialized.trans rfl⟩
  filter := filterGenerated h
  short := shortGenerated h
  stf := ⟨stfSession h, stfTransmits h⟩
  reference := fun hcfg hhints _ hprogram _ _ htx => referenceTransmits hcfg hhints hprogram htx

/-- The whole-program filter property of the reference AL interpreter with the registered
NanoSwitch target: for every related program value, every host port and every three-byte
packet, the reference session transmits exactly `filtered`, at every sufficiently large fuel,
and no terminating run does otherwise. -/
theorem referenceFilter (h : PacketStateText) {cfg : Interp_al.Interp.Config} (hcfg : Reference cfg)
    (hhints : cfg.printHints = []) {vprogram : Lang.Il.value} (hprogram : Rel vprogram program)
    (port : Int) (hport : Core.Object.hostInt port = true) (b0 s d : UInt8) :
    ReferenceTransmits cfg vprogram [(port, hexText [b0, s, d])] (filtered port b0 s d) :=
  (certificate h).reference hcfg hhints hprogram _ _ ((certificate h).filter port hport b0 s d)

/-- The quoted program is related to its own encoding, the value the reference receives when
`check-consumer` confirms that encoding is the decoded export. -/
theorem programRel : Rel (toValue program) program := rfl

/-- info: 'ExampleProofs.NanoP4SrcAddrFilter.filterGenerated' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms filterGenerated

/-- info: 'ExampleProofs.NanoP4SrcAddrFilter.shortGenerated' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shortGenerated

/-- info: 'ExampleProofs.NanoP4SrcAddrFilter.programRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms programRel

/-- info: 'ExampleProofs.NanoP4SrcAddrFilter.certificate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate

/-- info: 'ExampleProofs.NanoP4SrcAddrFilter.referenceFilter' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceFilter

end ExampleProofs.NanoP4SrcAddrFilter
