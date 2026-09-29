import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Representation.SourceAlias
import P4SpecTec.Refine.Representation.SourceMixfix

/-!
Source container construction from independently valid fields and the exact quoted
set, pair and map signatures. No generated carrier or decoder defines these domains.
This is our own proof support, not an upstream mirror.
-/

namespace P4SpecTec.Refine.Representation.Source

open P4SpecTec.Lang.Il P4SpecTec.Domain

/-- Pointwise source validity gives the positional derivation for a homogeneous list. -/
theorem Values.replicate {spec externalDomain} (element : typ) (vs : List value)
    (valid : ∀ v ∈ vs, Valid spec externalDomain element.it v) :
    Values spec externalDomain (List.replicate vs.length element) vs := by
  induction vs with
  | nil => exact .nil
  | cons v vs ih =>
    exact .cons element v _ _ (valid v (by simp))
      (ih (by intro x hx; exact valid x (by simp [hx])))

/-- info: 'P4SpecTec.Refine.Representation.Source.Values.replicate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Values.replicate
#audit_axioms Values.replicate

/-- The source set constructor, retaining its declared element parameter and list order. -/
theorem setValid {spec externalDomain} (element : typ) (v contents : value)
    (declared : body spec "set" = some ([Q.i "K"], .VariantT
      [Q.tc (.Brack (Q.a .LBrace) (.Arg (Q.t (.IterT (Q.t (Q.varT "K" [])) .List)))
        (Q.a .RBrace)) "set" [Q.t (Q.varT "K" [])]]))
    (shape : v.it = .CaseV (.Brack (Q.a .LBrace) (.Arg contents) (Q.a .RBrace)))
    (payload : Valid spec externalDomain (.IterT element .List) contents) :
    Valid spec externalDomain (Q.varT "set" [element]) v := by
  refine .variant (Q.i "set") [element] [Q.i "K"] _ _
    [Q.t (.IterT element .List)] v _ declared (by exact List.mem_cons_self) shape rfl ?_ ?_
  · simp only [instantiatedFields, typcase.nottyp, Q.nt, Mixfix.args]
    refine ⟨rfl, .cons ?_ .nil⟩
    exact .iter _ _ _ (.bound (Q.i "K") element.it rfl)
  · simpa only [Mixfix.args] using
      (Values.cons (Q.t (.IterT element .List)) contents [] [] payload .nil)

/-- info: 'P4SpecTec.Refine.Representation.Source.setValid' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms setValid
#audit_axioms setValid

/-- The source pair constructor keeps two distinct positional field derivations. -/
theorem pairValid {spec externalDomain} (keyType valueType : typ) (v key item : value)
    (declared : body spec "pair" = some ([Q.i "K", Q.i "V"], .VariantT
      [Q.tc (.Seq [.Arg (Q.t (Q.varT "K" [])), .Atom (Q.a (.Operator ":")),
        .Arg (Q.t (Q.varT "V" []))]) "pair" [Q.t (Q.varT "K" []), Q.t (Q.varT "V" [])]]))
    (shape : v.it = .CaseV (.Seq [.Arg key, .Atom (Q.a (.Operator ":")), .Arg item]))
    (hk : Valid spec externalDomain keyType.it key)
    (hv : Valid spec externalDomain valueType.it item) :
    Valid spec externalDomain (Q.varT "pair" [keyType, valueType]) v := by
  refine .variant (Q.i "pair") [keyType, valueType] [Q.i "K", Q.i "V"] _ _
    [keyType, valueType] v _ declared (by exact List.mem_cons_self) shape rfl ?_ ?_
  · simp only [instantiatedFields, typcase.nottyp, Q.nt, Mixfix.args,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append]
    refine ⟨rfl, .cons ?_ (.cons ?_ .nil)⟩
    · exact .bound (Q.i "K") keyType.it rfl
    · exact .bound (Q.i "V") valueType.it rfl
  · simpa only [Mixfix.args, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append] using
      (Values.cons keyType key _ _ hk (.cons valueType item [] [] hv .nil))

/-- info: 'P4SpecTec.Refine.Representation.Source.pairValid' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairValid
#audit_axioms pairValid

/-- The map alias instantiates its two parameters simultaneously through set and pair. -/
theorem mapValid {spec externalDomain} (keyType valueType : typ) (v : value)
    (declared : body spec "map" = some ([Q.i "K", Q.i "V"], .PlainT
      (Q.t (Q.varT "set" [Q.t (Q.varT "pair"
        [Q.t (Q.varT "K" []), Q.t (Q.varT "V" [])])]))))
    (payload : Valid spec externalDomain
      (Q.varT "set" [Q.t (Q.varT "pair" [keyType, valueType])]) v) :
    Valid spec externalDomain (Q.varT "map" [keyType, valueType]) v := by
  refine .alias (Q.i "map") [keyType, valueType] [Q.i "K", Q.i "V"] _
    (Q.t (Q.varT "set" [Q.t (Q.varT "pair" [keyType, valueType])])) v declared
    ⟨rfl, .cons ?_ .nil⟩ payload
  refine .named (Q.i "set") _ _ rfl (.cons ?_ .nil)
  refine .named (Q.i "pair") _ _ rfl (.cons ?_ (.cons ?_ .nil))
  · exact .bound (Q.i "K") keyType.it rfl
  · exact .bound (Q.i "V") valueType.it rfl

/-- info: 'P4SpecTec.Refine.Representation.Source.mapValid' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapValid
#audit_axioms mapValid

/-- Inverting a source pair recovers its two field domains without equating metadata. -/
theorem pairFields {spec externalDomain} (keyType valueType : typ) (v : value)
    (declared : body spec "pair" = some ([Q.i "K", Q.i "V"], .VariantT
      [Q.tc (.Seq [.Arg (Q.t (Q.varT "K" [])), .Atom (Q.a (.Operator ":")),
        .Arg (Q.t (Q.varT "V" []))]) "pair" [Q.t (Q.varT "K" []), Q.t (Q.varT "V" [])]]))
    (valid : Valid spec externalDomain (Q.varT "pair" [keyType, valueType]) v)
    (sourceOnly : Domain.SourceOnly externalDomain "pair" := by source_only) :
    ∃ (tree : Mixfix.t value) (key item : value), v.it = .CaseV tree ∧
      Mixfix.eq_mixop tree (.Seq [.Arg (), .Atom (Q.a (.Operator ":")), .Arg ()]) = true ∧
      Mixfix.args tree = [key, item] ∧ Valid spec externalDomain keyType.it key ∧
      Valid spec externalDomain valueType.it item := by
  cases valid with
  | runtime name args v payload => exact absurd payload (sourceOnly v)
  | record name args parameters sourceFields instantiated v valueFields found =>
    simp [declared] at found
  | «alias» name args parameters definition instantiated v found =>
    simp [declared] at found
  | variant name args parameters cases constructor instantiated v tree
      found member shape mixop fields payload =>
    have heq := Option.some.inj (found.symm.trans declared)
    cases heq
    have ctor : constructor = _ := List.mem_singleton.mp member
    subst constructor
    simp only [instantiatedFields, typcase.nottyp, Q.nt, Mixfix.args,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
      List.nil_append] at fields
    obtain ⟨_, fields⟩ := fields
    cases fields with
    | cons first rest =>
      cases rest with
      | cons second rest =>
        cases rest
        have hk := first.boundResult (Q.i "K") rfl
        have hv := second.boundResult (Q.i "V") rfl
        generalize hargs : Mixfix.args tree = args at payload
        cases payload with
        | cons kt key ts vs keyValid tail =>
          cases tail with
          | cons vt item ts vs itemValid tail =>
            cases tail
            refine ⟨tree, key, item, shape, ?_, hargs, ?_, ?_⟩
            · exact mixopTrans _ _ _ mixop rfl
            · simpa only [hk] using keyValid
            · simpa only [hv] using itemValid

/-- info: 'P4SpecTec.Refine.Representation.Source.pairFields' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairFields
#audit_axioms pairFields

/-- Inverting a source set recovers the source-valid list with its exact element domain. -/
theorem setFields {spec externalDomain} (element : typ) (v : value)
    (declared : body spec "set" = some ([Q.i "K"], .VariantT
      [Q.tc (.Brack (Q.a .LBrace) (.Arg (Q.t (.IterT (Q.t (Q.varT "K" [])) .List)))
        (Q.a .RBrace)) "set" [Q.t (Q.varT "K" [])]]))
    (valid : Valid spec externalDomain (Q.varT "set" [element]) v)
    (sourceOnly : Domain.SourceOnly externalDomain "set" := by source_only) :
    ∃ (tree : Mixfix.t value) (contents : value), v.it = .CaseV tree ∧
      Mixfix.eq_mixop tree (.Brack (Q.a .LBrace) (.Arg ()) (Q.a .RBrace)) = true ∧
      Mixfix.args tree = [contents] ∧
      Valid spec externalDomain (.IterT element .List) contents := by
  cases valid with
  | runtime name args v payload => exact absurd payload (sourceOnly v)
  | record name args parameters sourceFields instantiated v valueFields found =>
    simp [declared] at found
  | «alias» name args parameters definition instantiated v found =>
    simp [declared] at found
  | variant name args parameters cases constructor instantiated v tree
      found member shape mixop fields payload =>
    have heq := Option.some.inj (found.symm.trans declared)
    cases heq
    have ctor : constructor = _ := List.mem_singleton.mp member
    subst constructor
    simp only [instantiatedFields, typcase.nottyp, Q.nt, Mixfix.args] at fields
    obtain ⟨_, fields⟩ := fields
    cases fields with
    | cons first rest =>
      cases rest
      obtain ⟨child, hc, hs⟩ := first.iterResult (Q.t (Q.varT "K" [])) .List
      have he := hs.boundResult (Q.i "K") rfl
      generalize hargs : Mixfix.args tree = args at payload
      cases payload with
      | cons ty contents ts vs contentValid tail =>
        cases tail
        refine ⟨tree, contents, shape, mixopTrans _ _ _ mixop rfl, hargs, ?_⟩
        rw [hc] at contentValid
        exact contentValid.iterElement he

/-- info: 'P4SpecTec.Refine.Representation.Source.setFields' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms setFields
#audit_axioms setFields

/-- Map inversion preserves each substituted field syntax without identifying its metadata. -/
theorem mapPayload {spec externalDomain} (keyType valueType : typ) (v : value)
    (declared : body spec "map" = some ([Q.i "K", Q.i "V"], .PlainT
      (Q.t (Q.varT "set" [Q.t (Q.varT "pair"
        [Q.t (Q.varT "K" []), Q.t (Q.varT "V" [])])]))))
    (valid : Valid spec externalDomain (Q.varT "map" [keyType, valueType]) v)
    (sourceOnly : Domain.SourceOnly externalDomain "map" := by source_only) :
    ∃ keyType' valueType' : typ, keyType'.it = keyType.it ∧ valueType'.it = valueType.it ∧
      Valid spec externalDomain
        (Q.varT "set" [Q.t (Q.varT "pair" [keyType', valueType'])]) v := by
  obtain ⟨instantiated, fields, payload⟩ := valid.plainPayload declared sourceOnly
  obtain ⟨_, fields⟩ := fields
  cases fields with
  | cons sub rest =>
    cases rest
    obtain ⟨setArgs, result, arguments⟩ := sub.namedArguments (Q.i "set") _ rfl
    cases arguments with
    | cons pairSub rest =>
      cases rest
      obtain ⟨pairArgs, pairResult, pairArguments⟩ :=
        pairSub.namedArguments (Q.i "pair") _ rfl
      cases pairArguments with
      | cons keySub rest =>
        cases rest with
        | cons itemSub rest =>
          cases rest
          have hk := keySub.boundResult (Q.i "K") rfl
          have hv := itemSub.boundResult (Q.i "V") rfl
          refine ⟨_, _, hk, hv, ?_⟩
          rw [result] at payload
          apply payload.arguments
          simpa only [List.map_cons, List.map_nil, Q.t, Util.Source.mkPhrase] using
            congrArg (fun t : typ' => [t]) pairResult

/-- info: 'P4SpecTec.Refine.Representation.Source.mapPayload' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapPayload
#audit_axioms mapPayload

end P4SpecTec.Refine.Representation.Source
