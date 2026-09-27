import P4SpecTec.Codegen.Reify

/-!
Source-derived codecs for polymorphic single-constructor containers. Parameter admission
is supplied by complete source codecs, without bounding recursive parameter carriers.
-/

namespace P4SpecTec.Codegen.RepresentationContainers

open Std (Format)
open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Codegen.Types

/-- The checked source shape of a two-parameter positional container. -/
def pairShape (env : Env) (d : Lang.Al.def) :
    Except String (id × id × typcase) := do
  let .TypD name [left, right] definition _ := d.it
    | throw "pair codec needs exactly two source parameters"
  if left.it == right.it then throw "pair codec needs distinct source parameters"
  if env.representation.hasRawExtern name.it then
    throw "pair codec needs separate source/runtime admission"
  let .VariantT [constructor] := definition.it
    | throw "pair codec needs one source constructor"
  let [typ'.VarT a [], typ'.VarT b []] :=
      (Mixfix.args constructor.nottyp.it).map (fun t : typ => t.it)
    | throw "pair codec needs exactly two direct parameter fields"
  if a.it != left.it || b.it != right.it then
    throw "pair codec needs fields in parameter order"
  return (left, right, constructor)

private def pairTemplate : String :=
  "/-- Admitted values inherit both independently specified parameter domains. -/\n" ++
  "def NAME.admitted {α β : Type} (left : α → Prop) (right : β → Prop) : QUALIFIED α β → Prop\n" ++
  "  | .CTOR x y => left x ∧ right y\n" ++
  "\n" ++
  "private def NAME.sourceConstructor : typcase := SOURCE_CASE\n" ++
  "\nprivate theorem NAME.sourceArgs : Mixfix.args NAME.sourceConstructor.nottyp.it =\n" ++
  "    SOURCE_FIELDS := by\n" ++
  "  simp [NAME.sourceConstructor, typcase.nottyp, Q.tc, Q.nt, Mixfix.args]\n" ++
  "\n" ++
  "#audit_axioms NAME.sourceArgs\n\n" ++
  "private theorem NAME.sourceFields (leftType rightType : Lang.Il.typ) (v : Lang.Il.value)\n" ++
  "    (valid : Valid LIB.spec Representation.Source.externDomain\n" ++
  "      (Q.varT SOURCE_ID [leftType, rightType]) v) :\n" ++
  "    ∃ (tree : Mixfix.t Lang.Il.value) (a b : Lang.Il.value), v.it = .CaseV tree ∧\n" ++
  "      Mixfix.eq_mixop tree\n" ++
  "        MIXOP = true ∧\n" ++
  "      Mixfix.args tree = [a,b] ∧\n" ++
  "      Valid LIB.spec Representation.Source.externDomain leftType.it a ∧\n" ++
  "      Valid LIB.spec Representation.Source.externDomain rightType.it b := by\n" ++
  "  obtain ⟨tree, shape, matching, payload⟩ := valid.singleConstructor\n" ++
  "    (Q.i SOURCE_ID) [leftType, rightType] [Q.i LEFT_ID, Q.i RIGHT_ID] " ++
  "NAME.sourceConstructor\n" ++
  "    [leftType, rightType] v (by rfl) (by\n" ++
  "      intro instantiated subs\n" ++
  "      unfold instantiatedFields at subs\n" ++
  "      rw [NAME.sourceArgs] at subs\n" ++
  "      obtain ⟨_, subs⟩ := subs\n" ++
  "      cases subs with\n" ++
  "      | cons first rest =>\n" ++
  "        cases rest with\n" ++
  "        | cons second rest =>\n" ++
  "          cases rest\n" ++
  "          refine .cons ?_ (.cons ?_ .nil)\n" ++
  "          · intro value hv\n" ++
  "            simpa only [first.boundResult (Q.i LEFT_ID) rfl] using hv\n" ++
  "          · intro value hv\n" ++
  "            simpa only [second.boundResult (Q.i RIGHT_ID) rfl] using hv)\n" ++
  "  generalize hargs : Mixfix.args tree = args at payload\n" ++
  "  cases payload with\n" ++
  "  | cons type a types values ha tail =>\n" ++
  "    cases tail with\n" ++
  "    | cons type b types values hb tail =>\n" ++
  "      cases tail\n" ++
  "      exact ⟨tree, a, b, shape, mixopTrans _ _ _ matching rfl, hargs, ha, hb⟩\n" ++
  "\n" ++
  "#audit_axioms NAME.sourceFields\n\n" ++
  "/-- Complete source codec for every legal pair of parameter codecs. -/\n" ++
  "theorem NAME.codec {α β : Type} [ToValue α] [OfValue α] [ToValue β] [OfValue β]\n" ++
  "    (leftType rightType : Lang.Il.typ) (left : α → Prop) (right : β → Prop)\n" ++
  "    (leftCodec : Representation.Codec (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain" ++
  " leftType.it) left)\n" ++
  "    (rightCodec : Representation.Codec\n" ++
  "      (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain rightType.it) right) :\n" ++
  "    @Representation.Codec (QUALIFIED α β) ⟨QUALIFIED.toValue⟩\n" ++
  "      ⟨QUALIFIED.ofValue⟩\n" ++
  "      (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain (Q.varT SOURCE_ID [leftType, " ++
  "rightType]))\n" ++
  "      (NAME.admitted left right) := by\n" ++
  "  letI : ToValue (QUALIFIED α β) := ⟨QUALIFIED.toValue⟩\n" ++
  "  letI : OfValue (QUALIFIED α β) := ⟨QUALIFIED.ofValue⟩\n" ++
  "  constructor\n" ++
  "  · intro x hx\n" ++
  "    cases x with\n" ++
  "    | CTOR a b =>\n" ++
  "      refine Valid.variant (Q.i SOURCE_ID) [leftType, rightType] [Q.i LEFT_ID, Q.i " ++
  "RIGHT_ID]\n" ++
  "        [NAME.sourceConstructor] NAME.sourceConstructor [leftType, rightType] _\n" ++
  "        ENCODED_TREE (by rfl) (by exact List.mem_cons_self) rfl rfl ?_ ?_\n" ++
  "      · unfold instantiatedFields\n" ++
  "        rw [NAME.sourceArgs]\n" ++
  "        exact ⟨rfl, .cons (.bound (Q.i LEFT_ID) leftType.it rfl)\n" ++
  "          (.cons (.bound (Q.i RIGHT_ID) rightType.it rfl) .nil)⟩\n" ++
  "      · simp only [show Mixfix.args ENCODED_TREE =\n" ++
  "          [ToValue.toValue a, ToValue.toValue b] by simp [Mixfix.args]]\n" ++
  "        exact .cons leftType _ _ _ (leftCodec.encodingValid a hx.1)\n" ++
  "          (.cons rightType _ _ _ (rightCodec.encodingValid b hx.2) .nil)\n" ++
  "  · constructor\n" ++
  "    · intro fuel v x hv hd\n" ++
  "      obtain ⟨tree, a, b, shape, matching, fields, ha, hb⟩ :=\n" ++
  "        NAME.sourceFields leftType rightType v hv\n" ++
  "      have args : Prelude.Value.caseArgs tree\n" ++
  "          MIXOP = some [a,b] := by\n" ++
  "        simp [Prelude.Value.caseArgs, matching, fields]\n" ++
  "      cases fuel with\n" ++
  "      | zero => cases hd\n" ++
  "      | succ fuel =>\n" ++
  "        simp only [OfValue.ofValue, QUALIFIED.ofValue, shape, args] at hd\n" ++
  "        cases da : OfValue.ofValue (α := α) fuel a with\n" ++
  "        | none => simp [da] at hd\n" ++
  "        | some a' =>\n" ++
  "          cases db : OfValue.ofValue (α := β) fuel b with\n" ++
  "          | none => simp [da, db] at hd\n" ++
  "          | some b' =>\n" ++
  "            simp only [da, db] at hd\n" ++
  "            change some (QUALIFIED.CTOR a' b') = some x at hd\n" ++
  "            cases Option.some.inj hd\n" ++
  "            obtain ⟨aa, ra⟩ := leftCodec.decoder.sound fuel a a' ha da\n" ++
  "            obtain ⟨ab, rb⟩ := rightCodec.decoder.sound fuel b b' hb db\n" ++
  "            refine ⟨⟨aa, ab⟩, ?_⟩\n" ++
  "            change Rel v (QUALIFIED.toValue (.CTOR a' b'))\n" ++
  "            apply caseRelation (rendered := DECODED_TREE) shape (by rfl)\n" ++
  "            · exact mixopTrans _ _ _ matching rfl\n" ++
  "            · simp [fields, Mixfix.args, canons]\n" ++
  "              rw [show canon a = canon (ToValue.toValue a') from ra,\n" ++
  "                show canon b = canon (ToValue.toValue b') from rb] <;> simp\n" ++
  "    · intro v hv\n" ++
  "      obtain ⟨tree, a, b, shape, matching, fields, ha, hb⟩ :=\n" ++
  "        NAME.sourceFields leftType rightType v hv\n" ++
  "      obtain ⟨a', boundA, da⟩ := leftCodec.decoder.sufficient a ha\n" ++
  "      obtain ⟨b', boundB, db⟩ := rightCodec.decoder.sufficient b hb\n" ++
  "      refine ⟨.CTOR a' b', boundA + boundB + 1, ?_⟩\n" ++
  "      intro fuel hbound\n" ++
  "      have args : Prelude.Value.caseArgs tree\n" ++
  "          MIXOP = some [a,b] := by\n" ++
  "        simp [Prelude.Value.caseArgs, matching, fields]\n" ++
  "      cases fuel with\n" ++
  "      | zero => omega\n" ++
  "      | succ fuel =>\n" ++
  "        have da' := da fuel (by omega)\n" ++
  "        have db' := db fuel (by omega)\n" ++
  "        simp only [OfValue.ofValue, QUALIFIED.ofValue, shape, args]\n" ++
  "        rw [da', db']\n" ++
  "        rfl\n" ++
  "#audit_axioms QUALIFIED.codec\n"

private def pairContract : String :=
  "∀ {α β : Type} [ToValue α] [OfValue α] [ToValue β] [OfValue β]\n" ++
  "    (leftType rightType : Lang.Il.typ) (left : α → Prop) (right : β → Prop)\n" ++
  "    (leftCodec : Representation.Codec (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain" ++
  " leftType.it) left)\n" ++
  "    (rightCodec : Representation.Codec\n" ++
  "      (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain rightType.it) right),\n" ++
  "    @Representation.Codec (QUALIFIED α β) ⟨QUALIFIED.toValue⟩\n" ++
  "      ⟨QUALIFIED.ofValue⟩\n" ++
  "      (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain (Q.varT SOURCE_ID [leftType, " ++
  "rightType]))\n" ++
  "      (NAME.admitted left right)"

/-- The checked shape of a one-parameter container holding its element list. -/
def listShape (env : Env) (d : Lang.Al.def) : Except String (id × typcase) := do
  let .TypD name [element] definition _ := d.it
    | throw "list-container codec needs one source parameter"
  if env.representation.hasRawExtern name.it then
    throw "list-container codec needs separate source/runtime admission"
  let .VariantT [constructor] := definition.it
    | throw "list-container codec needs one source constructor"
  let [typ'.IterT child .List] :=
      (Mixfix.args constructor.nottyp.it).map (fun t : typ => t.it)
    | throw "list-container codec needs one list field"
  let .VarT parameter [] := child.it
    | throw "list-container codec needs a direct parameter element"
  if parameter.it != element.it then throw "list-container codec needs its declared parameter"
  return (element, constructor)

private def listTemplate : String :=
  "/-- Admitted containers have independently admitted elements. -/\n" ++
  "def NAME.admitted {α : Type} (element : α → Prop) : QUALIFIED α → Prop\n" ++
  "  | .CTOR xs => ∀ x ∈ xs, element x\n" ++
  "\n" ++
  "private def NAME.sourceConstructor : typcase := SOURCE_CASE\n" ++
  "\nprivate theorem NAME.sourceArgs : Mixfix.args NAME.sourceConstructor.nottyp.it =\n" ++
  "    SOURCE_FIELDS := by\n" ++
  "  simp [NAME.sourceConstructor, typcase.nottyp, Q.tc, Q.nt, Mixfix.args]\n" ++
  "\n" ++
  "#audit_axioms NAME.sourceArgs\n\n" ++
  "private theorem NAME.sourceFields (element : Lang.Il.typ) (v : Lang.Il.value)\n" ++
  "    (valid : Valid LIB.spec " ++
  "Representation.Source.externDomain (Q.varT SOURCE_ID [element]) v) :\n" ++
  "    ∃ (tree : Mixfix.t Lang.Il.value) (a : Lang.Il.value), v.it = .CaseV tree ∧\n" ++
  "      Mixfix.eq_mixop tree\n" ++
  "        MIXOP = true ∧\n" ++
  "      Mixfix.args tree = [a] ∧\n" ++
  "      Valid LIB.spec Representation.Source.externDomain (.IterT element .List) a := by\n" ++
  "  obtain ⟨tree, shape, matching, payload⟩ := valid.singleConstructor\n" ++
  "    (Q.i SOURCE_ID) [element] [Q.i LEFT_ID] NAME.sourceConstructor [Q.t (.IterT element " ++
  ".List)] v\n" ++
  "    (by rfl) (by\n" ++
  "      intro instantiated subs\n" ++
  "      unfold instantiatedFields at subs\n" ++
  "      rw [NAME.sourceArgs] at subs\n" ++
  "      obtain ⟨_, subs⟩ := subs\n" ++
  "      cases subs with\n" ++
  "      | cons first rest =>\n" ++
  "        cases rest\n" ++
  "        obtain ⟨child, hc, hs⟩ := first.iterResult (Q.t (Q.varT LEFT_ID [])) .List\n" ++
  "        have he := hs.boundResult (Q.i LEFT_ID) rfl\n" ++
  "        refine .cons ?_ .nil\n" ++
  "        intro value hv\n" ++
  "        rw [hc] at hv\n" ++
  "        exact hv.iterElement he)\n" ++
  "  generalize hargs : Mixfix.args tree = args at payload\n" ++
  "  cases payload with\n" ++
  "  | cons type a types values ha tail =>\n" ++
  "    cases tail\n" ++
  "    exact ⟨tree, a, shape, mixopTrans _ _ _ matching rfl, hargs, ha⟩\n" ++
  "\n" ++
  "#audit_axioms NAME.sourceFields\n\n" ++
  "/-- Complete source codec for every legal element codec. -/\n" ++
  "theorem NAME.codec {α : Type} [ToValue α] [OfValue α]\n" ++
  "    (element : Lang.Il.typ) (accepted : α → Prop)\n" ++
  "    (elementCodec : Representation.Codec\n" ++
  "      (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain element.it) accepted) :\n" ++
  "    @Representation.Codec (QUALIFIED α) ⟨QUALIFIED.toValue⟩\n" ++
  "      ⟨QUALIFIED.ofValue⟩\n" ++
  "      (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain (Q.varT SOURCE_ID " ++
  "[element]))\n" ++
  "      (NAME.admitted accepted) := by\n" ++
  "  letI : ToValue (QUALIFIED α) := ⟨QUALIFIED.toValue⟩\n" ++
  "  letI : OfValue (QUALIFIED α) := ⟨QUALIFIED.ofValue⟩\n" ++
  "  have contentsCodec := listCodec element accepted elementCodec\n" ++
  "  constructor\n" ++
  "  · intro x hx\n" ++
  "    cases x with\n" ++
  "    | CTOR xs =>\n" ++
  "      refine Valid.variant (Q.i SOURCE_ID) [element] [Q.i LEFT_ID] [NAME.sourceConstructor] " ++
  "NAME.sourceConstructor\n" ++
  "        [Q.t (.IterT element .List)] _\n" ++
  "        ENCODED_TREE (by rfl) (by exact List.mem_cons_self) rfl rfl ?_ ?_\n" ++
  "      · unfold instantiatedFields\n" ++
  "        rw [NAME.sourceArgs]\n" ++
  "        exact ⟨rfl, .cons (.iter _ _ _ (.bound (Q.i LEFT_ID) element.it rfl)) .nil⟩\n" ++
  "      · simpa [Mixfix.args] using\n" ++
  "          (Values.cons (Q.t (.IterT element .List)) _ [] []\n" ++
  "            (contentsCodec.encodingValid xs hx) .nil)\n" ++
  "  · constructor\n" ++
  "    · intro fuel v x hv hd\n" ++
  "      obtain ⟨tree, a, shape, matching, fields, ha⟩ := NAME.sourceFields element v hv\n" ++
  "      have args : Prelude.Value.caseArgs tree\n" ++
  "          MIXOP =\n" ++
  "            some [a] := by\n" ++
  "        simp [Prelude.Value.caseArgs, matching, fields]\n" ++
  "      cases fuel with\n" ++
  "      | zero => cases hd\n" ++
  "      | succ fuel =>\n" ++
  "        simp only [OfValue.ofValue, QUALIFIED.ofValue, shape, args] at hd\n" ++
  "        change (do let a' ← OfValue.ofValue (α := List α) fuel a\n" ++
  "                   pure (QUALIFIED.CTOR a')) = some x at hd\n" ++
  "        cases da : OfValue.ofValue (α := List α) fuel a with\n" ++
  "        | none => simp [da] at hd\n" ++
  "        | some a' =>\n" ++
  "          simp only [da] at hd\n" ++
  "          change some (QUALIFIED.CTOR a') = some x at hd\n" ++
  "          cases Option.some.inj hd\n" ++
  "          obtain ⟨aa, ra⟩ := contentsCodec.decoder.sound fuel a a' ha da\n" ++
  "          refine ⟨aa, ?_⟩\n" ++
  "          change Rel v (QUALIFIED.toValue (.CTOR a'))\n" ++
  "          apply caseRelation (rendered := DECODED_TREE) shape (by rfl)\n" ++
  "          · exact mixopTrans _ _ _ matching rfl\n" ++
  "          · simp [fields, Mixfix.args, canons]\n" ++
  "            rw [show canon a = canon (ToValue.toValue a') from ra]\n" ++
  "    · intro v hv\n" ++
  "      obtain ⟨tree, a, shape, matching, fields, ha⟩ := NAME.sourceFields element v hv\n" ++
  "      obtain ⟨a', boundA, da⟩ := contentsCodec.decoder.sufficient a ha\n" ++
  "      refine ⟨.CTOR a', boundA + 1, ?_⟩\n" ++
  "      intro fuel hbound\n" ++
  "      have args : Prelude.Value.caseArgs tree\n" ++
  "          MIXOP =\n" ++
  "            some [a] := by\n" ++
  "        simp [Prelude.Value.caseArgs, matching, fields]\n" ++
  "      cases fuel with\n" ++
  "      | zero => omega\n" ++
  "      | succ fuel =>\n" ++
  "        have da' := da fuel (by omega)\n" ++
  "        simp only [OfValue.ofValue, QUALIFIED.ofValue, shape, args]\n" ++
  "        change (do let a' ← OfValue.ofValue (α := List α) fuel a\n" ++
  "                   pure (QUALIFIED.CTOR a')) = _\n" ++
  "        rw [da']\n" ++
  "        rfl\n" ++
  "#audit_axioms QUALIFIED.codec\n"

private def listContract : String :=
  "∀ {α : Type} [ToValue α] [OfValue α]\n" ++
  "    (element : Lang.Il.typ) (accepted : α → Prop)\n" ++
  "    (elementCodec : Representation.Codec\n" ++
  "      (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain element.it) accepted),\n" ++
  "    @Representation.Codec (QUALIFIED α) ⟨QUALIFIED.toValue⟩\n" ++
  "      ⟨QUALIFIED.ofValue⟩\n" ++
  "      (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain (Q.varT SOURCE_ID " ++
  "[element]))\n" ++
  "      (NAME.admitted accepted)"

private def instantiate (env : Env) (d : Lang.Al.def) (template : String) :
    Except String String := do
  let (left, right, constructor, isList) ← match pairShape env d with
    | .ok (left, right, constructor) => pure (left, right, constructor, false)
    | .error _ => do
      let (element, constructor) ← listShape env d
      pure (element, element, constructor, true)
  let name := Names.typeName d.it.id.it
  let ctor := (ctorNames [constructor]).head!
  let (origin, arguments) := match constructor.typorigin.it with | .mk o args => (o, args)
  let sourceCase := Term.call "Q.tc" [Reify.mixfix constructor.nottyp.it Reify.typ,
    Reify.str origin.it, Reify.lst (arguments.map Reify.typ)]
  let mixop := Mixfix.to_mixop constructor.nottyp.it
  let encoded := mixfixTerm mixop (if isList then [.atom "(ToValue.toValue xs)"]
    else [.atom "(ToValue.toValue a)", .atom "(ToValue.toValue b)"])
  let decoded := mixfixTerm mixop (if isList then [.atom "(ToValue.toValue a')"]
    else [.atom "(ToValue.toValue a')", .atom "(ToValue.toValue b')"])
  return template
    |>.replace "SOURCE_CASE" sourceCase.fmt.pretty
    |>.replace "SOURCE_FIELDS" (Reify.lst ((Mixfix.args constructor.nottyp.it).map
      Reify.typ)).fmt.pretty
    |>.replace "ENCODED_TREE" encoded.arg.pretty
    |>.replace "DECODED_TREE" decoded.arg.pretty
    |>.replace "MIXOP" (mixopTerm mixop).arg.pretty
    |>.replace "SOURCE_ID" (Reify.str d.it.id.it).fmt.pretty
    |>.replace "LEFT_ID" (Reify.str left.it).fmt.pretty
    |>.replace "RIGHT_ID" (Reify.str right.it).fmt.pretty
    |>.replace "QUALIFIED" (env.q name)
    |>.replace "NAME" name
    |>.replace "LIB" env.lib
    |>.replace "CTOR" ctor

/-- Exact quantified codec obligation for the generated dictionaries. -/
def codecType (env : Env) (d : Lang.Al.def) : Except String Format := do
  return Format.text (← instantiate env d
    (if (pairShape env d).isOk then pairContract else listContract))

private def pairEncodingTemplate : String := "
/-- Encoded pair validity is exactly independent validity of both encoded parameters. -/
theorem NAME.encodingSourceIff {α β : Type} [ToValue α] [ToValue β]
    (leftType rightType : Lang.Il.typ) (x : QUALIFIED α β) :
    Valid LIB.spec Representation.Source.externDomain
      (Q.varT SOURCE_ID [leftType, rightType]) (QUALIFIED.toValue x) ↔
    NAME.admitted
      (fun a => Valid LIB.spec Representation.Source.externDomain leftType.it (ToValue.toValue a))
      (fun b => Valid LIB.spec Representation.Source.externDomain
        rightType.it (ToValue.toValue b)) x := by
  cases x with
  | CTOR a b =>
    constructor
    · intro valid
      obtain ⟨tree, va, vb, shape, _matching, fields, ha, hb⟩ := NAME.sourceFields _ _ _ valid
      have same : ENCODED_TREE = tree := Lang.Il.value'.CaseV.inj shape
      subst tree
      have args : [ToValue.toValue a, ToValue.toValue b] = [va, vb] := by
        simpa only [Mixfix.args, List.flatMap_cons, List.flatMap_nil,
          List.nil_append, List.cons_append] using fields
      rcases List.cons.inj args with ⟨rfl, tail⟩
      rcases List.cons.inj tail with ⟨rfl, _⟩
      exact ⟨ha, hb⟩
    · intro accepted
      refine Valid.variant (Q.i SOURCE_ID) [leftType, rightType] [Q.i LEFT_ID, Q.i RIGHT_ID]
        [NAME.sourceConstructor] NAME.sourceConstructor [leftType, rightType] _
        ENCODED_TREE (by rfl) (by exact List.mem_cons_self) rfl rfl ?_ ?_
      · unfold instantiatedFields
        rw [NAME.sourceArgs]
        exact ⟨rfl, .cons (.bound (Q.i LEFT_ID) leftType.it rfl)
          (.cons (.bound (Q.i RIGHT_ID) rightType.it rfl) .nil)⟩
      · simpa only [Mixfix.args, List.flatMap_cons, List.flatMap_nil,
          List.nil_append, List.cons_append] using
          (Values.cons leftType _ _ _ accepted.1 (Values.cons rightType _ _ _ accepted.2 .nil))

#audit_axioms NAME.encodingSourceIff
"

private def listEncodingTemplate : String := "
/-- Encoded container validity is exactly independent validity of every encoded element. -/
theorem NAME.encodingSourceIff {α : Type} [ToValue α]
    (element : Lang.Il.typ) (x : QUALIFIED α) :
    Valid LIB.spec Representation.Source.externDomain
      (Q.varT SOURCE_ID [element]) (QUALIFIED.toValue x) ↔
    NAME.admitted
      (fun a => Valid LIB.spec Representation.Source.externDomain
        element.it (ToValue.toValue a)) x := by
  cases x with
  | CTOR xs =>
    constructor
    · intro valid
      obtain ⟨tree, contents, shape, _matching, fields, ha⟩ := NAME.sourceFields _ _ valid
      have same : ENCODED_TREE = tree := Lang.Il.value'.CaseV.inj shape
      subst tree
      have args : [ToValue.toValue xs] = [contents] := by
        simpa only [Mixfix.args, List.flatMap_cons, List.flatMap_nil,
          List.nil_append, List.cons_append] using fields
      cases (List.cons.inj args).1
      exact (Representation.Source.encodedListIff element xs).mp ha
    · intro accepted
      refine Valid.variant (Q.i SOURCE_ID) [element] [Q.i LEFT_ID]
        [NAME.sourceConstructor] NAME.sourceConstructor [Q.t (.IterT element .List)] _
        ENCODED_TREE (by rfl) (by exact List.mem_cons_self) rfl rfl ?_ ?_
      · unfold instantiatedFields
        rw [NAME.sourceArgs]
        exact ⟨rfl, .cons (.iter _ _ _ (.bound (Q.i LEFT_ID) element.it rfl)) .nil⟩
      · simpa only [Mixfix.args, List.flatMap_cons, List.flatMap_nil,
          List.nil_append, List.cons_append] using
          (Values.cons (Q.t (.IterT element .List)) _ [] []
            ((Representation.Source.encodedListIff element xs).mpr accepted) .nil)

#audit_axioms NAME.encodingSourceIff
"

/-- Emit source inversion and a codec quantified over arbitrary legal parameter codecs. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String Format := do
  let core := if (pairShape env d).isOk then pairTemplate else listTemplate
  let encoded := if (pairShape env d).isOk then pairEncodingTemplate else listEncodingTemplate
  let proof ← instantiate env d
    (core.trimAsciiEnd.toString ++ "\n\n" ++ encoded.trimAscii.toString)
  return Format.text (boundedLines ("open Lang.Il Domain Representation.Source\n\n" ++ proof))

end P4SpecTec.Codegen.RepresentationContainers
