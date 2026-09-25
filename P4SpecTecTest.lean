import P4SpecTecTest.Smoke

/-!
# P4SpecTecTest

Test-only modules for the core library: mirror checks against upstream,
prelude builtins against their OCaml originals, decode round-trips,
`#guard_msgs` files. Nothing here is imported by a client. This root imports
every module under `P4SpecTecTest/`; `scripts/check-imports.sh` enforces it.
-/
