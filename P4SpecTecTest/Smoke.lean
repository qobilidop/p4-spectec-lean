/-!
Smoke test: the test library builds under `lake test` and the two check
idioms the project uses, `#guard` for computations and `#guard_msgs` for
expected messages, work with the pinned toolchain.
-/

#guard 1 + 1 == 2

/-- info: 'Nat.zero_add' does not depend on any axioms -/
#guard_msgs in #print axioms Nat.zero_add
