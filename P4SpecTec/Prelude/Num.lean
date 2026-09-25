/-!
Numeric operations of the meta-language. Mirrors `Num.bin` and `Num.un`
of `p4spec/lib/lang/xl/num.ml` on Lean's `Nat` and `Int`: subtraction of
naturals yields an integer, division and modulus truncate toward zero as
`Bigint` does, and exponentiation is `Nat` exponentiation.
-/

namespace P4SpecTec.Prelude.Num

/-- `Num.bin `SubOp` on naturals: the result is an integer. -/
def natSub (a b : Nat) : Int := (a : Int) - (b : Int)

/-- `Num.bin `DivOp` on naturals; `none` on zero, where upstream's
`assert false` aborts. -/
def natDiv? (a b : Nat) : Option Nat := if b == 0 then none else some (a / b)

/-- `Num.bin `ModOp` on naturals; `none` on zero. -/
def natMod? (a b : Nat) : Option Nat := if b == 0 then none else some (a % b)

/-- `Num.bin `DivOp` on integers: `Bigint./` truncates toward zero; `none` on zero. -/
def intDiv? (a b : Int) : Option Int := if b == 0 then none else some (Int.tdiv a b)

/-- `Num.bin `ModOp` on integers: `Bigint.rem` keeps the dividend's sign; `none` on zero. -/
def intMod? (a b : Int) : Option Int := if b == 0 then none else some (Int.tmod a b)

/-- `Num.bin` has no `PowOp` case upstream (`assert false`), so `^` is a
failure in the executable encoding too. -/
def pow? {α : Type} (_a _b : α) : Option α := none

/-- The downcast `int` to `nat` of the interpreter's `downcast`: only
non-negative integers. -/
def toNat? (i : Int) : Option Nat := if i ≥ 0 then some i.toNat else none

end P4SpecTec.Prelude.Num
