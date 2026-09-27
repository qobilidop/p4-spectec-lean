import P4SpecTec.Codegen.Certificates.RepresentationRecursive

/-! Conditional list and option codec proofs for the actual recursive field dictionaries. -/

namespace P4SpecTec.Codegen.RepresentationRecursive

open P4SpecTec.Lang.Il P4SpecTec.Codegen.Types

private def listProofs (index child : Nat) (family : Family) : String :=
  let helper := family.encoderUnfolding.headD ""
  let encoding := if helper.isEmpty then "  rfl\n" else
    s!"  have payload : ∀ xs, {helper} xs = xs.map (encode .f{child}) := by\n" ++
    "    intro xs\n    induction xs with\n" ++
    s!"    | nil => simp only [{helper}, List.map_nil]\n" ++
    "    | cons x xs ih =>\n" ++
    s!"      simp only [{helper}, List.map_cons]\n" ++
    "      exact congrArg (List.cons _) ih\n" ++
    "  dsimp only [encode]\n  rw [payload]\n  rfl\n"
  s!"private theorem listEncoding{index} (xs : Carrier .f{index}) :\n" ++
  s!"    (encode .f{index} xs).it = .ListV (xs.map (encode .f{child})) := by\n" ++
  encoding ++ s!"\n#audit_axioms listEncoding{index}\n\n" ++
  s!"private theorem listDecoding{index} (fuel : Nat) (v : value) (raws : List value)\n" ++
  "    (shape : v.it = .ListV raws) :\n" ++
  s!"    decode .f{index} fuel v = raws.mapM (decode .f{child} fuel) := by\n" ++
  "  cases v\n  cases shape\n  rfl\n\n" ++
  s!"#audit_axioms listDecoding{index}\n\n" ++
  s!"private theorem soundList{index} (v : value) (raws : List value)\n" ++
  "    (shape : v.it = .ListV raws)\n" ++
  s!"    (children : ∀ raw ∈ raws, ∀ fuel x, decode .f{child} fuel raw = some x →\n" ++
  s!"      admitted .f{child} x ∧ Rel raw (encode .f{child} x))\n" ++
  s!"    (fuel : Nat) (xs : Carrier .f{index})\n" ++
  s!"    (decoded : decode .f{index} fuel v = some xs) :\n" ++
  s!"    admitted .f{index} xs ∧ Rel v (encode .f{index} xs) := by\n" ++
  s!"  rw [listDecoding{index} fuel v raws shape] at decoded\n" ++
  s!"  have paired := Representation.mapMForall₂ (decode .f{child} fuel) decoded\n" ++
  s!"  have checked : admitted .f{index} xs ∧\n" ++
  s!"      canons raws = canons (xs.map (encode .f{child})) := by\n" ++
  "    clear decoded shape\n    induction paired with\n" ++
  "    | nil => exact ⟨.nil, rfl⟩\n" ++
  "    | @cons raw x raws xs head tail ih =>\n" ++
  "      obtain ⟨accepted, related⟩ := children raw (by simp) fuel x head\n" ++
  "      obtain ⟨acceptedTail, relatedTail⟩ := ih (by\n" ++
  "        intro raw member\n        exact children raw (by simp [member]))\n" ++
  "      refine ⟨.cons x xs accepted acceptedTail, ?_⟩\n" ++
  s!"      change canon raw = canon (encode .f{child} x) at related\n" ++
  "      simp only [List.map_cons, canons, related, relatedTail]\n" ++
  "  refine ⟨checked.1, ?_⟩\n" ++
  "  change canon v = canon (encode _ xs)\n" ++
  s!"  simp only [canon, shape, listEncoding{index}, canon', checked.2]\n\n" ++
  s!"#audit_axioms soundList{index}\n\n" ++
  s!"private theorem decodeList{index} (v : value) (raws : List value)\n" ++
  s!"    (xs : Carrier .f{index}) (shape : v.it = .ListV raws)\n" ++
  s!"    (children : List.Forall₂ (Representation.Decodes (decode .f{child})) raws xs) :\n" ++
  s!"    Representation.Decodes (decode .f{index}) v xs := by\n" ++
  s!"  letI : OfValue (Carrier .f{child}) := ⟨decode .f{child}⟩\n" ++
  "  obtain ⟨bound, stable⟩ := Representation.decodesList children v.note v.at\n" ++
  "  refine ⟨bound, ?_⟩\n  intro fuel large\n" ++
  s!"  rw [listDecoding{index} fuel v raws shape]\n" ++
  "  exact stable fuel large\n\n" ++
  s!"#audit_axioms decodeList{index}\n"

private def optionProofs (index child : Nat) (family : Family) : String :=
  let expose := "  dsimp only [encode]\n" ++
    (if family.encoderUnfolding.isEmpty then "" else
      "  unfold " ++ " ".intercalate family.encoderUnfolding ++ "\n") ++ "  rfl\n"
  s!"private theorem noneEncoding{index} :\n" ++
  s!"    (encode .f{index} none).it = .OptV none := by\n" ++ expose ++
  s!"\n#audit_axioms noneEncoding{index}\n\n" ++
  s!"private theorem someEncoding{index} (x : Carrier .f{child}) :\n" ++
  s!"    (encode .f{index} (some x)).it = .OptV (some (encode .f{child} x)) := by\n" ++
  expose ++ s!"\n#audit_axioms someEncoding{index}\n\n" ++
  s!"private theorem noneDecoding{index} (fuel : Nat) (v : value)\n" ++
  "    (shape : v.it = .OptV none) :\n" ++
  s!"    decode .f{index} fuel v = some none := by\n" ++
  "  cases v\n  cases shape\n  rfl\n\n" ++
  s!"#audit_axioms noneDecoding{index}\n\n" ++
  s!"private theorem someDecoding{index} (fuel : Nat) (v raw : value)\n" ++
  "    (shape : v.it = .OptV (some raw)) :\n" ++
  s!"    decode .f{index} fuel v = (decode .f{child} fuel raw).map some := by\n" ++
  "  cases v\n  cases shape\n  rfl\n\n" ++
  s!"#audit_axioms someDecoding{index}\n\n" ++
  s!"private theorem soundNone{index} (v : value) (shape : v.it = .OptV none)\n" ++
  s!"    (fuel : Nat) (x : Carrier .f{index})\n" ++
  s!"    (decoded : decode .f{index} fuel v = some x) :\n" ++
  s!"    admitted .f{index} x ∧ Rel v (encode .f{index} x) := by\n" ++
  s!"  rw [noneDecoding{index} fuel v shape] at decoded\n" ++
  "  cases Option.some.inj decoded\n  refine ⟨.none, ?_⟩\n" ++
  s!"  change canon v = canon (encode .f{index} none)\n" ++
  s!"  simp only [canon, shape, noneEncoding{index}, canon']\n\n" ++
  s!"#audit_axioms soundNone{index}\n\n" ++
  s!"private theorem soundSome{index} (v raw : value)\n" ++
  "    (shape : v.it = .OptV (some raw))\n" ++
  s!"    (child : ∀ fuel x, decode .f{child} fuel raw = some x →\n" ++
  s!"      admitted .f{child} x ∧ Rel raw (encode .f{child} x))\n" ++
  s!"    (fuel : Nat) (x : Carrier .f{index})\n" ++
  s!"    (decoded : decode .f{index} fuel v = some x) :\n" ++
  s!"    admitted .f{index} x ∧ Rel v (encode .f{index} x) := by\n" ++
  s!"  rw [someDecoding{index} fuel v raw shape] at decoded\n" ++
  s!"  cases found : decode .f{child} fuel raw with\n" ++
  "  | none => rw [found] at decoded; cases decoded\n" ++
  "  | some payload =>\n    rw [found] at decoded\n" ++
  "    cases Option.some.inj decoded\n" ++
  "    obtain ⟨accepted, related⟩ := child fuel payload found\n" ++
  "    refine ⟨.some payload accepted, ?_⟩\n" ++
  s!"    change canon v = canon (encode .f{index} (some payload))\n" ++
  s!"    change canon raw = canon (encode .f{child} payload) at related\n" ++
  s!"    simp only [canon, shape, someEncoding{index}, canon']\n" ++
  "    simpa only [canon] using congrArg (fun inner =>\n" ++
  "      (⟨.OptV (some inner), dummy, P4SpecTec.Util.Source.no_region⟩ : value)) related\n\n" ++
  s!"#audit_axioms soundSome{index}\n\n" ++
  s!"private theorem decodeNone{index} (v : value) (shape : v.it = .OptV none) :\n" ++
  s!"    Representation.Decodes (decode .f{index}) v none :=\n" ++
  s!"  ⟨0, fun fuel _ => noneDecoding{index} fuel v shape⟩\n\n" ++
  s!"#audit_axioms decodeNone{index}\n\n" ++
  s!"private theorem decodeSome{index} (v raw : value) (x : Carrier .f{child})\n" ++
  "    (shape : v.it = .OptV (some raw))\n" ++
  s!"    (child : Representation.Decodes (decode .f{child}) raw x) :\n" ++
  s!"    Representation.Decodes (decode .f{index}) v (some x) := by\n" ++
  "  obtain ⟨bound, stable⟩ := child\n  refine ⟨bound, ?_⟩\n  intro fuel large\n" ++
  s!"  rw [someDecoding{index} fuel v raw shape, stable fuel large]\n  rfl\n\n" ++
  s!"#audit_axioms decodeSome{index}\n"

/-- Emit conditional actual list/option field equations, fidelity and stable decoding. -/
def iterationDeclarations (_env : Env) (plan : Plan) (namespaceName : String) :
    Except String Std.Format := do
  let mut declarations := []
  for (family, index) in plan.families.toList.zipIdx do
    if family.leaf.isSome then continue
    match family.source.it with
    | .IterT _ .List =>
      let [child] := family.children | throw "recursive list proof needs exactly one child"
      if family.guarded then throw "recursive list proof does not add a nominal fuel frame"
      declarations := declarations ++ [listProofs index child family]
    | .IterT _ .Opt =>
      let [child] := family.children | throw "recursive option proof needs exactly one child"
      if family.guarded then throw "recursive option proof does not add a nominal fuel frame"
      declarations := declarations ++ [optionProofs index child family]
    | _ => pure ()
  pure (Std.Format.text (boundedLines (
    s!"namespace {namespaceName}\n\n" ++ "\n\n".intercalate declarations ++
    s!"\nend {namespaceName}")))

end P4SpecTec.Codegen.RepresentationRecursive
