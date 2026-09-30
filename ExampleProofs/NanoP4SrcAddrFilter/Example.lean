import ExampleProofs.NanoP4SrcAddrFilter.Certificate

/-!
# A whole Nano-P4 program, proved from its export

This checked walkthrough concerns the pinned upstream test program
`nano-p4/testdata/positive/src-addr-filter.p4`:

```p4
parser Parser(packet_in pkt, out Header hdr) {
    state start { pkt.extract(hdr.nanonet); transition accept; }
}
control Filter(inout Header hdr, out bool pass) {
    table src_acl {
        key = { hdr.nanonet.src : exact; }
        actions = { allow(pass); deny(pass); }
        const entries = { (8w1) : allow(pass); (8w2) : allow(pass); (8w3) : deny(pass); }
    }
    apply { pass = false; src_acl.apply(); }
}
NanoSwitch(Parser(), Filter()) main;
```

## From export to theorem

Upstream parses and elaborates the program; `exports/programs/nano-p4/positive/` holds the
resulting AL value. `Program.lean` quotes it as a typed term of the generated model, written by
`nano-program-quote` and compared with the decoded export by `check-consumer`. Nothing about
the program is restated by hand.

`Evaluation.lean` evaluates the generated model on it with `lazy_eval`: `NanoSwitch_init` types
the program, loads it and builds the evaluation context (`initialized`); each theorem then
drives packets through `NanoSwitch_drive`, whose parser calls the concrete target's `extract`
and whose control applies the table. The evaluation unfolds the generated `partial_fixpoint`
definitions one equation at a time and every step is checked by the kernel.

Packets are STF-style hexadecimal texts of bytes. Evaluation treats every byte as a symbolic
value: the `drop`, `packetType` and `dst` header fields stay unevaluated terms throughout, so
one theorem covers all of them. The source address is decided either by a concrete value
(`forwardOne`, `forwardTwo`, `denyThree`) or, for the other 253 values, by `omega` from the
facts that it is none of 1, 2 or 3 (`dropUnlisted`), after the source byte's bits are read back
as its value (`bits_to_int_unsigned_bytesBits`).

## What is assumed

Only `PacketStateText`: extract decodes the driver's packet state through Lean's JSON printer
and parser, both `partial` and therefore opaque to proofs. It is tested on sample states and
exercised by every replayed corpus packet, but it is a premise, stated in every theorem that
runs extract.

## The headline theorems
-/

namespace ExampleProofs.NanoP4SrcAddrFilter.Walkthrough

open P4SpecTec P4SpecTec.BackendSim P4SpecTec.Refine NanoP4Target ExampleProofs.NanoP4SrcAddrFilter

/-- The generated model filters every three-byte packet by its source address. -/
example (h : PacketStateText) (port : Int) (hport : Core.Object.hostInt port = true)
    (b0 s d : UInt8) :
    Transmits program [(port, hexText [b0, s, d])]
      (if s.toNat = 1 ∨ s.toNat = 2 then [[(port, hexText [b0, s, d])]] else [[]]) :=
  (certificate h).filter port hport b0 s d

/-- So does the reference AL interpreter with the registered NanoSwitch target, at every
sufficiently large fuel, and no terminating run disagrees. -/
example (h : PacketStateText) {cfg : Interp_al.Interp.Config} (hcfg : Reference cfg)
    (hhints : cfg.printHints = []) {vprogram : Lang.Il.value} (hprogram : Rel vprogram program)
    (b0 d : UInt8) :
    ReferenceTransmits cfg vprogram [(7, hexText [b0, 2, d])] [[(7, hexText [b0, 2, d])]] :=
  referenceFilter h hcfg hhints hprogram 7 rfl b0 2 d

/-- A packet with an unlisted source is dropped by the reference interpreter. -/
example (h : PacketStateText) {cfg : Interp_al.Interp.Config} (hcfg : Reference cfg)
    (hhints : cfg.printHints = []) {vprogram : Lang.Il.value} (hprogram : Rel vprogram program) :
    ReferenceTransmits cfg vprogram [(0, hexText [0, 10, 0])] [[]] :=
  referenceFilter h hcfg hhints hprogram 0 rfl 0 10 0

/-!
## Repeating the checks

From the repository root, `nix develop --command scripts/check.sh` builds the certificate,
runs `check-consumer` and the colocated mutation tests. For focused work:

```sh
nix develop --command lake build --wfail ExampleProofs.NanoP4SrcAddrFilter.Example
nix develop --command lake exe check-consumer
nix develop --command python3 ExampleProofs/NanoP4SrcAddrFilter/test/run.py
```
-/

end ExampleProofs.NanoP4SrcAddrFilter.Walkthrough
