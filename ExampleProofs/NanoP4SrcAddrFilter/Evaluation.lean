import ExampleProofs.NanoP4SrcAddrFilter.Program
import NanoP4Target.Packet
import NanoP4Target.Session
import P4SpecTec.Tactic.LazyEval

/-!
# Generated sessions of the source-address filter

Whole-program evaluation of the generated Nano-P4 model with the concrete NanoSwitch target,
from the exported program through `NanoSwitch_init` (typing, loading and the evaluation
context) and packet driving. `lazy_eval` computes every step with kernel-checked proofs.
Header fields other than the source address stay symbolic throughout.

Packets are STF-style hexadecimal texts of symbolic bytes. Every theorem that runs extract
assumes `PacketStateText`, the text round trip of the driver's packet state through Lean's
`partial` JSON printer and parser; no other assumption is made.
-/

namespace ExampleProofs.NanoP4SrcAddrFilter

open P4SpecTec P4SpecTec.BackendSim NanoP4Target

/-- The outcome of `NanoSwitch_init` on the program, as evaluated. -/
def initialOutcome : Option (Except Prelude.Fail NanoP4Spec.evalContext) :=
  lazy_eval% NanoP4Spec.NanoSwitch_init.run program

/-- The initialization outcome is `initialOutcome`, a successful evaluation context. -/
theorem initialized : NanoP4Spec.NanoSwitch_init.run program = initialOutcome := by
  lazy_eval

/-- The rules every packet evaluation uses: initialization, the packet-state text premise and
hexadecimal decoding. -/
macro "evaluate_session" h:term : tactic =>
  `(tactic| (unfold Transmits; apply Exists.intro
             lazy_eval [initialized, packetStateText $h, string_to_bits_hexText]))

/-- The same, for a symbolic port in the host integer range. -/
macro "evaluate_session" h:term "at" hport:term : tactic =>
  `(tactic| (unfold Transmits; apply Exists.intro
             lazy_eval [initialized, $hport, packetStateText $h, string_to_bits_hexText]))

/-- A three-byte packet whose source address is 1 is forwarded unchanged on its port, whatever
its other header fields. -/
theorem forwardOne (h : PacketStateText) (port : Int) (hport : Core.Object.hostInt port = true)
    (b0 d : UInt8) :
    Transmits program [(port, hexText [b0, 1, d])] [[(port, hexText [b0, 1, d])]] := by
  evaluate_session h at hport

/-- A three-byte packet whose source address is 2 is forwarded unchanged. -/
theorem forwardTwo (h : PacketStateText) (port : Int) (hport : Core.Object.hostInt port = true)
    (b0 d : UInt8) :
    Transmits program [(port, hexText [b0, 2, d])] [[(port, hexText [b0, 2, d])]] := by
  evaluate_session h at hport

/-- A three-byte packet whose source address is 3 hits the `deny` entry and is dropped. -/
theorem denyThree (h : PacketStateText) (port : Int) (hport : Core.Object.hostInt port = true)
    (b0 d : UInt8) :
    Transmits program [(port, hexText [b0, 3, d])] [[]] := by
  evaluate_session h at hport

/-- A three-byte packet whose source address has no table entry misses the table and is
dropped. The table key is the source byte's value (`bits_to_int_unsigned_bytesBits`), and
`omega` decides the entry comparisons from the facts about it. -/
theorem dropUnlisted (h : PacketStateText) (port : Int) (hport : Core.Object.hostInt port = true)
    (b0 s d : UInt8) (h1 : s.toNat ≠ 1) (h2 : s.toNat ≠ 2) (h3 : s.toNat ≠ 3) :
    Transmits program [(port, hexText [b0, s, d])] [[]] := by
  unfold Transmits; apply Exists.intro
  lazy_eval [initialized, hport, packetStateText h, string_to_bits_hexText,
    bits_to_int_unsigned_bytesBits, h1, h2, h3, s.toNat_lt]

/-- A packet shorter than the Nanonet header leaves the header at its default, misses the table
and is dropped: two bytes. -/
theorem dropTwoBytes (h : PacketStateText) (port : Int) (hport : Core.Object.hostInt port = true)
    (b0 b1 : UInt8) :
    Transmits program [(port, hexText [b0, b1])] [[]] := by
  evaluate_session h at hport

/-- One byte is dropped. -/
theorem dropOneByte (h : PacketStateText) (port : Int) (hport : Core.Object.hostInt port = true)
    (b0 : UInt8) :
    Transmits program [(port, hexText [b0])] [[]] := by
  evaluate_session h at hport

/-- The empty packet is dropped. -/
theorem dropEmpty (h : PacketStateText) (port : Int) (hport : Core.Object.hostInt port = true) :
    Transmits program [(port, hexText [])] [[]] := by
  evaluate_session h at hport

/-- The packets of the pinned STF session: `000100`, `000300` and `000A00` on port 0. -/
def stfPackets : List Runtime.Sim.Io.rx :=
  [(0, hexText [0, 1, 0]), (0, hexText [0, 3, 0]), (0, hexText [0, 10, 0])]

set_option maxHeartbeats 4000000 in
/-- The outcome of the STF session, as evaluated. `check-consumer` compares its transmissions
and final context, which holds the raw extern receiver of the last extract, with the pinned
upstream simulator's recorded session. -/
def stfOutcome :
    Option (Except Prelude.Fail (NanoP4Spec.evalContext × List (List Runtime.Sim.Io.tx))) :=
  lazy_eval% assuming (h : PacketStateText), (session program stfPackets).run
    using [initialized, packetStateText h, string_to_bits_hexText]

set_option maxHeartbeats 4000000 in
/-- The STF session's outcome is `stfOutcome`, context threaded through all three packets. -/
theorem stfSession (h : PacketStateText) : (session program stfPackets).run = stfOutcome := by
  lazy_eval [initialized, packetStateText h, string_to_bits_hexText]

/-- The STF session forwards `000100` unchanged on port 0 and drops `000300` and `000A00`. -/
theorem stfTransmits (h : PacketStateText) :
    Transmits program stfPackets [[(0, hexText [0, 1, 0])], [], []] :=
  ⟨_, (stfSession h).trans rfl⟩

end ExampleProofs.NanoP4SrcAddrFilter
