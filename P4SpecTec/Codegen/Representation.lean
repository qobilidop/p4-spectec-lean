/-!
Explicit runtime-carrier extensions. These affect generated Lean storage only;
the exported AL definitions and their source membership remain unchanged.
-/

namespace P4SpecTec.Codegen

/-- Representation choices supplied explicitly to generation. -/
structure Representation where
  /-- Monomorphic variants that additionally carry a raw runtime extern. -/
  rawExternTypes : List String := []
  deriving BEq, Repr

/-- Reserved constructor for the runtime-only raw-extern alternative. -/
def Representation.rawExternCtor : String := "runtimeExtern"

/-- Whether this source type has the raw-extern runtime alternative. -/
def Representation.hasRawExtern (r : Representation) (id : String) : Bool :=
  r.rawExternTypes.contains id

end P4SpecTec.Codegen
