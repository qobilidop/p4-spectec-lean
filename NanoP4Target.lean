import NanoP4Target.Contract
import NanoP4Target.Externs
import NanoP4Target.Packet
import NanoP4Target.Session

/-!
# NanoP4Target

The concrete NanoSwitch target connected to the generated Nano-P4 model: the typed extern
instance, the proof that it discharges the core's extern contract against the reference
target registered in the AL interpreter, and two-way composition of packet sessions from
semantic initialization through packet processing. Hexadecimal packet inputs and the
trusted text boundary of packet decoding support whole-program statements.
-/
