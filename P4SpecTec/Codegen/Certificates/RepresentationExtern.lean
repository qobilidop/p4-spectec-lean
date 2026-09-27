import P4SpecTec.Codegen.Certificates.RepresentationField

/-! Complete source codecs for declared opaque extern types and their exact JSON dictionaries. -/

namespace P4SpecTec.Codegen.RepresentationExterns

/-- Require an actual opaque source type declaration, rather than a runtime variant extension. -/
def checkSupport (d : Lang.Al.def) : Except String Unit := do
  let .ExternTypD .. := d.it | throw "source extern codec needs an external type declaration"

/-- The exact declared source extern obligation with canonical extern dictionaries. -/
def codecType (env : Env) (d : Lang.Al.def) : Except String Std.Format := do
  checkSupport d
  let type := Util.Source.mkPhrase (.VarT (Util.Source.mkPhrase d.it.id.it) [])
  let field ← RepresentationFields.resolve env (fun _ => none) type
  pure (Std.Format.text (field.type (RepresentationFields.source env type)))

/-- Emit the source extern codec from the pinned language's opaque JSON membership rule. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String Std.Format := do
  checkSupport d
  let type := Util.Source.mkPhrase (.VarT (Util.Source.mkPhrase d.it.id.it) [])
  let field ← RepresentationFields.resolve env (fun _ => none) type
  let name := Names.typeName d.it.id.it
  pure (Std.Format.text (boundedLines (
    "/-- Every declared opaque source value has its exact extern JSON representation. -/\n" ++
    s!"theorem {name}.codec : " ++ (← codecType env d).pretty 1000000 ++ " :=\n  " ++
    field.codec ++ s!"\n\n#audit_axioms {env.q name}.codec")))

end P4SpecTec.Codegen.RepresentationExterns
