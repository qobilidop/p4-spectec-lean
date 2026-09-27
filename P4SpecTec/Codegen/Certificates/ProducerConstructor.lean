import P4SpecTec.Codegen.Certificates.Producer

/-! Source-derived constructor admission lemmas for producer certificates. -/

namespace P4SpecTec.Codegen.ProducerConstructor
open P4SpecTec.Lang.Il P4SpecTec.Refine

/-- Prove admission of an actual encoded constructor from its independent field domains.
The encoder equations are checked; recursive list helpers receive proved map equations. -/
def declarations (env : Env) (name : String) (index : Nat) (theoremName : String) :
    Except String String := do
  let some info := env.types[name]? | throw "unknown"
  let some (.VariantT cases) := info.deftyp | throw "not variant"
  unless info.tparams.isEmpty do throw "producer constructor has open type parameters"
  let some c := cases[index]? | throw "bad index"
  let fields := Domain.Mixfix.args c.nottyp.it
  let ctor := (Types.ctorNames cases)[index]!
  let qualified := env.q (Names.typeName name)
  let caseTerm (c : typcase) :=
    let .mk origin args := c.typorigin.it
    (Term.call "Q.tc" [Reify.mixfix c.nottyp.it Reify.typ,
      Reify.str origin.it, Reify.lst (args.map Reify.typ)]).fmt.pretty 1000000
  let binders := (fields.zipIdx).map fun (f, i) =>
    s!"(p{i} : {(Types.typTerm env [] f.it).fmt.pretty})"
  let hs ← (fields.zipIdx).mapM fun (f, i) => do
    pure s!"(h{i} : {← Producer.admission env f s!"p{i}"})"
  let result ← Producer.admission env (Q.t (Q.varT name []))
    ("(" ++ qualified ++ "." ++ ctor ++ " " ++
      " ".intercalate ((List.range fields.length).map (fun i => s!"p{i}")) ++ ")")
  let fs := (Reify.lst (fields.map Reify.typ)).fmt.pretty 1000000
  let substitutions ← fields.mapM RepresentationFields.identitySubstitution
  let sub := substitutions.foldr (fun p ps => s!".cons ({p}) ({ps})") ".nil"
  let proof := (List.range fields.length).foldr
    (fun i rest => s!".cons _ _ _ _ h{i} ({rest})") ".nil"
  let member := (List.range index).foldr (fun _ s => "List.mem_cons_of_mem _ (" ++ s ++ ")")
    "List.mem_cons_self"
  pure (boundedLines (s!"private theorem {theoremName} " ++ " ".intercalate (binders ++ hs) ++
    " :\n    " ++ result ++ " := by\n" ++
    "  apply Representation.Source.Valid.variant (Q.i " ++ name.quote ++ ") [] []\n" ++
    "    [" ++ ", ".intercalate (cases.map caseTerm) ++ "]\n    (" ++ caseTerm c ++ ")\n" ++
    "    " ++ fs ++ " _ _ (by rfl)\n" ++
    "  · exact " ++ member ++ "\n  · rfl\n  · rfl\n" ++
    (if fields.isEmpty then
      "  · simpa [Lang.Il.typcase.nottyp, Domain.Mixfix.args] using\n" ++
      "      (show Representation.Source.instantiatedFields [] [] [] [] from ⟨rfl, .nil⟩)\n" ++
      "  · simpa [Domain.Mixfix.args] using (Representation.Source.Values.nil\n" ++
      "      (spec := " ++ env.lib ++ ".spec)\n" ++
      "      (externalDomain := Representation.Source.externDomain))\n" else
      "  · simp only [Lang.Il.typcase.nottyp, Domain.Mixfix.args, List.flatMap_cons, " ++
      "List.flatMap_nil, List.nil_append, List.cons_append]\n" ++
      "    exact ⟨rfl, " ++ sub ++ "⟩\n" ++
      "  · simp only [Domain.Mixfix.args, List.flatMap_cons, List.flatMap_nil, " ++
      "List.nil_append, List.cons_append]\n    first\n" ++
      "    | exact " ++ proof ++ "\n" ++
      "    | run_tac P4SpecTec.Tactic.encodingFacts `" ++ env.lib ++ "\n" ++
      "      simpa only [*] using (" ++ proof ++ ")\n") ++
    s!"#audit_axioms {theoremName}\n"))

end P4SpecTec.Codegen.ProducerConstructor
