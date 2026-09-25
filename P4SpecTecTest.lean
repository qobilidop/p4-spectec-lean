import P4SpecTecTest.Smoke
import P4SpecTecTest.Decode
import P4SpecTecTest.Builtins
import P4SpecTecTest.Quote
import P4SpecTecTest.QuoteChecks
import P4SpecTecTest.Subtypes
import P4SpecTecTest.Alter
import P4SpecTecTest.PrintPolicies
import P4SpecTecTest.Updates
import P4SpecTecTest.StateEval

/-!
# P4SpecTecTest

Test-only modules for the core library: mirror checks against upstream,
prelude builtins against their OCaml originals, decode round-trips,
`#guard_msgs` files. Nothing here is imported by a client. This root imports
every module under `P4SpecTecTest/` except the executables' `Main.lean`
roots (each defines `main`); `scripts/check-imports.sh` enforces it.
-/
