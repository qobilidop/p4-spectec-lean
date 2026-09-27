import P4SpecTec.BackendSim.Core.Func
import P4SpecTec.BackendSim.Core.Object
import P4SpecTec.BackendSim.NanoSwitch.Pipe
import P4SpecTec.BackendSim.SpecImpl.Func
import P4SpecTec.BackendSim.SpecImpl.Unpack

import P4SpecTec.Codegen.Attempt
import P4SpecTec.Codegen.Census
import P4SpecTec.Codegen.Certificates.Builtin
import P4SpecTec.Codegen.Certificates.CallAdmission
import P4SpecTec.Codegen.Certificates.Equality
import P4SpecTec.Codegen.Certificates.Forward
import P4SpecTec.Codegen.Certificates.Initialization
import P4SpecTec.Codegen.Certificates.Producer
import P4SpecTec.Codegen.Certificates.ProducerComposition
import P4SpecTec.Codegen.Certificates.ProducerConstructor
import P4SpecTec.Codegen.Certificates.ProducerContext
import P4SpecTec.Codegen.Certificates.ProducerContextCall
import P4SpecTec.Codegen.Certificates.ProducerContextProof
import P4SpecTec.Codegen.Certificates.ProducerDefault
import P4SpecTec.Codegen.Certificates.ProducerTotal
import P4SpecTec.Codegen.Certificates.ProducerUpdateCall
import P4SpecTec.Codegen.Certificates.Representation
import P4SpecTec.Codegen.Certificates.RepresentationAlias
import P4SpecTec.Codegen.Certificates.RepresentationConstructor
import P4SpecTec.Codegen.Certificates.RepresentationContainer
import P4SpecTec.Codegen.Certificates.RepresentationExtern
import P4SpecTec.Codegen.Certificates.RepresentationField
import P4SpecTec.Codegen.Certificates.RepresentationMap
import P4SpecTec.Codegen.Certificates.RepresentationMixedVariant
import P4SpecTec.Codegen.Certificates.RepresentationRecord
import P4SpecTec.Codegen.Certificates.RepresentationRecursive
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveAdmission
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveCodec
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveConstructor
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveEncoding
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveIteration
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveProof
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveSource
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveTotality
import P4SpecTec.Codegen.Certificates.RepresentationTotal
import P4SpecTec.Codegen.Certificates.RepresentationVariant
import P4SpecTec.Codegen.Certificates.Reverse
import P4SpecTec.Codegen.Certificates.RunSound
import P4SpecTec.Codegen.Certificates.SourceBuiltin
import P4SpecTec.Codegen.Certificates.SourceEntry
import P4SpecTec.Codegen.Certificates.SourcePolymorphic
import P4SpecTec.Codegen.Certificates.SourceProfile
import P4SpecTec.Codegen.Certificates.StateForward
import P4SpecTec.Codegen.Certificates.StateRunSound
import P4SpecTec.Codegen.Coverage
import P4SpecTec.Codegen.Coverage.Check
import P4SpecTec.Codegen.Emit
import P4SpecTec.Codegen.Env
import P4SpecTec.Codegen.Exp
import P4SpecTec.Codegen.Fmt
import P4SpecTec.Codegen.Funcs
import P4SpecTec.Codegen.Graph
import P4SpecTec.Codegen.Keywords
import P4SpecTec.Codegen.Mode
import P4SpecTec.Codegen.Names
import P4SpecTec.Codegen.PrintHints
import P4SpecTec.Codegen.Props
import P4SpecTec.Codegen.QuoteCheck
import P4SpecTec.Codegen.Reify
import P4SpecTec.Codegen.Rels
import P4SpecTec.Codegen.StateProps
import P4SpecTec.Codegen.Types

import P4SpecTec.Domain.Atom
import P4SpecTec.Domain.Mixfix

import P4SpecTec.Interface.Builtin.Call
import P4SpecTec.Interface.Builtin.Ints
import P4SpecTec.Interface.Builtin.Lists
import P4SpecTec.Interface.Builtin.Maps
import P4SpecTec.Interface.Builtin.Nats
import P4SpecTec.Interface.Builtin.Numerics
import P4SpecTec.Interface.Builtin.Sets
import P4SpecTec.Interface.Builtin.Texts
import P4SpecTec.Interface.P4.Unparse

import P4SpecTec.Interp.Effects
import P4SpecTec.Interp.InterpAl.Backtrack
import P4SpecTec.Interp.InterpAl.Ctx
import P4SpecTec.Interp.InterpAl.Interp

import P4SpecTec.Lang.Al.Ast
import P4SpecTec.Lang.Al.Json
import P4SpecTec.Lang.Hints.Alter
import P4SpecTec.Lang.Hints.AlterJson
import P4SpecTec.Lang.Hints.Input
import P4SpecTec.Lang.Il.Ast
import P4SpecTec.Lang.Il.Json
import P4SpecTec.Lang.Xl.Bool
import P4SpecTec.Lang.Xl.Num

import P4SpecTec.Prelude
import P4SpecTec.Prelude.Eval
import P4SpecTec.Prelude.Extern
import P4SpecTec.Prelude.Iter
import P4SpecTec.Prelude.Num
import P4SpecTec.Prelude.StateEval
import P4SpecTec.Prelude.Value

import P4SpecTec.Refine.Builtin.Collection
import P4SpecTec.Refine.Builtin.Invoke
import P4SpecTec.Refine.Builtin.List
import P4SpecTec.Refine.Builtin.Map
import P4SpecTec.Refine.Builtin.Numeric
import P4SpecTec.Refine.Builtin.Set
import P4SpecTec.Refine.Builtin.Text
import P4SpecTec.Refine.Calc
import P4SpecTec.Refine.Call
import P4SpecTec.Refine.Init
import P4SpecTec.Refine.Iteration
import P4SpecTec.Refine.IterationColumns
import P4SpecTec.Refine.IterationLength
import P4SpecTec.Refine.IterationPrem
import P4SpecTec.Refine.Print
import P4SpecTec.Refine.Producer
import P4SpecTec.Refine.ProducerMap
import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Realize
import P4SpecTec.Refine.RealizeFuel
import P4SpecTec.Refine.RealizeInterp
import P4SpecTec.Refine.Representation
import P4SpecTec.Refine.Representation.Delay
import P4SpecTec.Refine.Representation.Equality
import P4SpecTec.Refine.Representation.Source
import P4SpecTec.Refine.Representation.SourceAlias
import P4SpecTec.Refine.Representation.SourceAtomic
import P4SpecTec.Refine.Representation.SourceCodec
import P4SpecTec.Refine.Representation.SourceContainer
import P4SpecTec.Refine.Representation.SourceExtern
import P4SpecTec.Refine.Representation.SourceMixfix
import P4SpecTec.Refine.Representation.SourceObservation
import P4SpecTec.Refine.Representation.SourcePrimitive
import P4SpecTec.Refine.Representation.SourceRecord
import P4SpecTec.Refine.Representation.SourceSubst
import P4SpecTec.Refine.Representation.SourceTuple
import P4SpecTec.Refine.Representation.SourceVariant
import P4SpecTec.Refine.SourceBuiltin
import P4SpecTec.Refine.SourceProfile
import P4SpecTec.Refine.StateCalc
import P4SpecTec.Refine.StateInterp
import P4SpecTec.Refine.StateNormalize
import P4SpecTec.Refine.StateRules
import P4SpecTec.Refine.Subtype
import P4SpecTec.Refine.Value
import P4SpecTec.Refine.ValueOrder

import P4SpecTec.Runtime.Dynamic.Var
import P4SpecTec.Runtime.DynamicAl.Func
import P4SpecTec.Runtime.DynamicAl.Rel
import P4SpecTec.Runtime.Sim.Io
import P4SpecTec.Runtime.Type.Equiv
import P4SpecTec.Runtime.Type.Expand
import P4SpecTec.Runtime.Type.Subst
import P4SpecTec.Runtime.Type.SubstDepth
import P4SpecTec.Runtime.Type.Typ
import P4SpecTec.Runtime.Type.Typdef
import P4SpecTec.Runtime.Value.Match
import P4SpecTec.Runtime.Value.Value

import P4SpecTec.Tactic.Audit
import P4SpecTec.Tactic.CarrierInduction
import P4SpecTec.Tactic.Det
import P4SpecTec.Tactic.Encoding
import P4SpecTec.Tactic.IterationColumns
import P4SpecTec.Tactic.Monotonicity
import P4SpecTec.Tactic.OutcomeInduction
import P4SpecTec.Tactic.Realize
import P4SpecTec.Tactic.Refine
import P4SpecTec.Tactic.RunSound
import P4SpecTec.Tactic.StateRefine
import P4SpecTec.Tactic.StateRunSound

import P4SpecTec.Util.ByteText
import P4SpecTec.Util.Source
import P4SpecTec.Util.Yojson

/-!
# P4SpecTec

The core library: the deep embedding of P4-SpecTec's IL and AL
(`P4SpecTec.Lang.Il`, `P4SpecTec.Lang.Al`), its semantics ported from upstream's AL
interpreter (`P4SpecTec.Interp_al`, TRUSTED, with the runtime it needs under
`Runtime/` and `Interface/`), the runtime the generated code imports
(`P4SpecTec.Prelude`), the code generator (`P4SpecTec.Codegen`), and the
tactics that discharge generated theorems (`P4SpecTec.Tactic`).

Layout and principles: `docs/design.md`. A module whose path is an upstream
OCaml path, capitalised, mirrors that file (`Lang/Il/Ast.lean` mirrors
`lang/il/ast.ml`) under upstream's module name as its namespace, and says
so; `scripts/check-mirror.py` derives the pairs from the paths.
-/
