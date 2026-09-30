import P4SpecTec.Tactic.LazyEval

/-! Lazy evaluation: `partial_fixpoint` and well-founded recursion, free variables, rules. -/

namespace P4SpecTecTest.Tactic.LazyEval

/-- A `partial_fixpoint` function, which neither `decide` nor the kernel can reduce. -/
def collatz (n : Nat) : Option Nat :=
  if n ≤ 1 then some 0
  else if n % 2 = 0 then do return (← collatz (n / 2)) + 1
  else do return (← collatz (3 * n + 1)) + 1
partial_fixpoint

theorem collatz27 : collatz 27 = some 111 := by lazy_eval

/-- info: 'P4SpecTecTest.Tactic.LazyEval.collatz27' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms collatz27

/-- A well-founded traversal of a 64-element array. Checking the definitional gaps naively
makes the kernel unfold `Array.mapM.map` through its accessibility proofs, exponentially in
the array size. -/
theorem mapM64 :
    (Array.replicate 64 true).mapM (fun b => (pure (!b) : Except String Bool)) =
      .ok (Array.replicate 64 false) := by
  lazy_eval

/-- Free variables stay symbolic; natural-number arithmetic around them is still folded. -/
theorem symbolic (b : UInt8) (xs : List Bool) :
    ((collatz 6).map (· + b.toNat),
      decide ((#[b.toNat % 2 == 1, xs.isEmpty].size : Int) < 2 ^ 62)) =
      (some (8 + b.toNat), true) := by
  lazy_eval

/-- An opaque function, specified only by a conditional rule. -/
opaque secret : Nat → Nat

-- A rule whose condition is discharged by evaluation; the head stays folded otherwise.
example (h : ∀ n, n % 2 = 0 → secret n = n + 1) : (collatz 4).map (fun k => secret (k + 2)) =
    some 5 := by
  lazy_eval [h]

-- A hypothesis about a free variable is a rule in terms of that variable.
example (x : Nat) (hx : secret x = 7) : [secret x, (collatz 2).getD 0] = [7, 1] := by
  lazy_eval [hx]

-- A stuck Boolean test on a free variable is decided by `omega` from facts.
example (x : Nat) (h : x ≠ 3) (hlt : x < 10) :
    (if x % 16 == 3 then 1 else collatz 4 |>.getD 0) = 2 := by
  lazy_eval [h, hlt]

/-- A value evaluated once and reused. -/
def collatz27Value : Option Nat := lazy_eval% collatz 27

#guard collatz27Value == some 111

/-- A value evaluated with a rule that mentions an assumption. -/
def secretFive : Option Nat :=
  lazy_eval% assuming (h : ∀ n, n % 2 = 0 → secret n = n + 1),
    (collatz 4).map (fun k => secret (k + 2)) using [h]

/-- info: def P4SpecTecTest.Tactic.LazyEval.secretFive : Option Nat :=
some 5 -/
#guard_msgs in #print secretFive

/-- error: lazy_eval%: the value depends on its assumptions
  h -/
#guard_msgs in
example : 1 = 1 := lazy_eval% assuming (h : 1 = 1), h

/-- error: lazy_eval: evaluated to
  some 111
which is not
  some 112
innermost stuck subterm:
  some 111 -/
#guard_msgs in example : collatz 27 = some 112 := by lazy_eval

end P4SpecTecTest.Tactic.LazyEval
