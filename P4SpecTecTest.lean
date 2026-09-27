import P4SpecTecTest.BackendSim.NanoSwitch.Target

import P4SpecTecTest.Codegen.Certificates.StateForward
import P4SpecTecTest.Codegen.Coverage
import P4SpecTecTest.Codegen.CoverageChecks
import P4SpecTecTest.Codegen.Monotonicity
import P4SpecTecTest.Codegen.PrintHints
import P4SpecTecTest.Codegen.QuoteChecks
import P4SpecTecTest.Codegen.State
import P4SpecTecTest.Codegen.StateProps
import P4SpecTecTest.Codegen.Subtypes
import P4SpecTecTest.Codegen.Updates

import P4SpecTecTest.Interface.Builtins

import P4SpecTecTest.Interp.InterpAl.State

import P4SpecTecTest.Lang.Al.Decode
import P4SpecTecTest.Lang.Hints.Alter

import P4SpecTecTest.Prelude.StateEval

import P4SpecTecTest.Refine.GeneratedState
import P4SpecTecTest.Refine.NanoTargetRepresentation
import P4SpecTecTest.Refine.Print
import P4SpecTecTest.Refine.Realize
import P4SpecTecTest.Refine.RecursivePrefix
import P4SpecTecTest.Refine.StateCalc
import P4SpecTecTest.Refine.StateInterp
import P4SpecTecTest.Refine.StateRules

import P4SpecTecTest.Runtime.Type

import P4SpecTecTest.Util.ByteText

/-!
# P4SpecTecTest

Test-only modules for the core library: mirror checks against upstream,
prelude builtins against their OCaml originals, decode round-trips,
`#guard_msgs` files. Nothing here is imported by a client. This root imports
the unit tests. Registered oracle executables own their runner modules;
`scripts/check-library-boundaries.py` checks transitive build reachability.
-/
