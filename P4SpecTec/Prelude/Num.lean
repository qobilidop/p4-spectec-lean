/-!
Numeric operations of the meta-language. Mirrors `Num.bin` and `Num.un`
of `p4spec/lib/lang/xl/num.ml` on Lean's `Nat` and `Int`: subtraction of
naturals yields an integer, division and modulus truncate toward zero as
`Bigint` does, and exponentiation is `Nat` exponentiation.
-/

namespace P4SpecTec.Prelude.Num

/-- `Num.bin `SubOp` on naturals: the result is an integer. -/
def natSub (a b : Nat) : Int := (a : Int) - (b : Int)

/-- `Num.bin `DivOp` on integers: `Bigint./` truncates toward zero. -/
def intDiv (a b : Int) : Int := Int.tdiv a b

/-- `Num.bin `ModOp` on integers: `Bigint.rem` keeps the dividend's sign. -/
def intMod (a b : Int) : Int := Int.tmod a b

/-- `Num.bin `PowOp` on naturals. -/
def natPow (a b : Nat) : Nat := a ^ b

/-- `Num.bin `PowOp` on integers with a natural exponent, as `Bigint.pow`. -/
def intPow (a : Int) (b : Int) : Int := a ^ b.toNat

/-- The downcast `int` to `nat` of the interpreter's `downcast`: only
non-negative integers. -/
def toNat? (i : Int) : Option Nat := if i ≥ 0 then some i.toNat else none

end P4SpecTec.Prelude.Num
