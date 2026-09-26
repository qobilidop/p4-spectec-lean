import P4SpecTec.Tactic.Refine.Forward

/-!
The tactic `refine_al` that discharges the generated refinement theorems
(design section 5.1, rung 3): the AL interpreter run on the quoted
definition refines the generated code. It is a lockstep symbolic
execution. The interpreter side is computed by `simp` with the
interpreter's own equations on the concrete quoted syntax, one fuel
level at a time (`cases` on the fuel; exhaustion refines anything); the
generated side is walked by the rules of `Refine/Calc.lean`: a `have`
binds its variable, a call of another definition is matched with the
interpreter's invocation through that definition's refinement theorem
(or the induction hypothesis inside a recursion group), an `if`
premise, a pattern match and a sequential choice are split on both
sides, and at a `pure` the results are related by computing `canon` on
both. The interpreter's values are related to the generated values by
facts `canon v = canon (toValue x)`; when the interpreter inspects a
value whose generated counterpart is a variable, that variable is
split by `cases`, which is the case analysis the generated code performs
too.

The tactic is generic: it knows nothing but the shapes the runtime,
the interpreter and the code generator fix, so a definition it cannot
close fails the build, which is what makes the generated theorem a check.
-/
