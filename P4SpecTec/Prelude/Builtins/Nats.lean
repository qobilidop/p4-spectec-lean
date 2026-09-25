/-!
Natural-number builtins. Mirrors `p4spec/lib/interface/builtin/nats.ml`.
-/

namespace P4SpecTec.Prelude.Builtins.Nats

/-- `dec $sum_nat(nat*) : nat`. -/
def sum_nat (ns : List Nat) : Nat := ns.sum

/-- `dec $max_nat(nat*) : nat`; `none` on the empty list, where upstream errors. -/
def max_nat (ns : List Nat) : Option Nat := ns.max?

/-- `dec $min_nat(nat*) : nat`; `none` on the empty list, where upstream errors. -/
def min_nat (ns : List Nat) : Option Nat := ns.min?

end P4SpecTec.Prelude.Builtins.Nats
