import P4SpecTec.Refine.Representation.SourceExtern
import P4SpecTec.Refine.Representation.SourceMixfix

/-! Independent source grammars respect the canonical observations used at call boundaries. -/

namespace P4SpecTec.Refine.Representation.Source
open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Util.Source

private theorem shapeBool {v w : value} {b : Bool} (shape : v.it = .BoolV b)
    (same : canon v = canon w) : w.it = .BoolV b := by
  cases hw : w.it <;> try (rename_i inner; cases inner)
  all_goals simp_all [canon, canon']

private theorem shapeNat {v w : value} {n : Nat} (shape : v.it = .NumV (.Nat n))
    (same : canon v = canon w) : w.it = .NumV (.Nat n) := by
  cases hw : w.it <;> try (rename_i inner; cases inner)
  all_goals simp_all [canon, canon']

private theorem shapeInt {v w : value} {n : Int} (shape : v.it = .NumV (.Int n))
    (same : canon v = canon w) : w.it = .NumV (.Int n) := by
  cases hw : w.it <;> try (rename_i inner; cases inner)
  all_goals simp_all [canon, canon']

private theorem shapeText {v w : value} {text : ByteText} (shape : v.it = .TextV text)
    (same : canon v = canon w) : w.it = .TextV text := by
  cases hw : w.it <;> try (rename_i inner; cases inner)
  all_goals simp_all [canon, canon']

private theorem shapeList {v w : value} {values : List value} (shape : v.it = .ListV values)
    (same : canon v = canon w) : ∃ ws, w.it = .ListV ws ∧ canons values = canons ws := by
  cases hw : w.it <;> try (rename_i inner; cases inner)
  all_goals simp_all [canon, canon']

private theorem shapeNone {v w : value} (shape : v.it = .OptV none)
    (same : canon v = canon w) : w.it = .OptV none := by
  cases hw : w.it <;> try (rename_i inner; cases inner)
  all_goals simp_all [canon, canon']

private theorem shapeSome {v w inner : value} (shape : v.it = .OptV (some inner))
    (same : canon v = canon w) : ∃ next, w.it = .OptV (some next) ∧ canon inner = canon next := by
  cases hw : w.it <;> try (rename_i inner; cases inner)
  all_goals simp_all [canon, canon']

private theorem shapeTuple {v w : value} {values : List value} (shape : v.it = .TupleV values)
    (same : canon v = canon w) : ∃ ws, w.it = .TupleV ws ∧ canons values = canons ws := by
  cases hw : w.it <;> try (rename_i inner; cases inner)
  all_goals simp_all [canon, canon']

private theorem shapeRecord {v w : value} {fields : List valuefield}
    (shape : v.it = .StructV fields) (same : canon v = canon w) :
    ∃ fs, w.it = .StructV fs ∧ canonFields fields = canonFields fs := by
  cases hw : w.it <;> try (rename_i inner; cases inner)
  all_goals simp_all [canon, canon']

private theorem shapeVariant {v w : value} {tree : Mixfix.t value}
    (shape : v.it = .CaseV tree) (same : canon v = canon w) :
    ∃ next, w.it = .CaseV next ∧ canonMixfix tree = canonMixfix next := by
  cases hw : w.it <;> try (rename_i inner; cases inner)
  all_goals simp_all [canon, canon']

private theorem recordFields {xs ys : List valuefield}
    (same : canonFields xs = canonFields ys) :
    xs.map (fun x => x.1.it) = ys.map (fun y => y.1.it) ∧
      canons (xs.map (·.2)) = canons (ys.map (·.2)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [canonFields, canons]
  | cons x xs ih =>
    cases ys with
    | nil => simp [canonFields] at same
    | cons y ys =>
      simp only [canonFields, List.cons.injEq, Prod.mk.injEq, info.mk.injEq,
        mkPhrase, and_true] at same
      obtain ⟨labels, values⟩ := ih same.2
      simp only [List.map_cons, canons, same.1.1, same.1.2, labels, values]
      exact ⟨True.intro, True.intro⟩

private theorem recordLabels {source : List typfield} {xs ys : List valuefield}
    (valid : List.Forall₂ (fun source actual => Atom.eq source.1.it actual.1.it = true)
      source xs) (same : xs.map (fun x => x.1.it) = ys.map (fun y => y.1.it)) :
    List.Forall₂ (fun source actual => Atom.eq source.1.it actual.1.it = true) source ys := by
  induction valid generalizing ys with
  | nil => cases ys <;> simp_all
  | @cons source x sources xs head tail ih =>
    cases ys with
    | nil => simp at same
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at same
      exact .cons (same.1 ▸ head) (ih same.2)

mutual
private theorem mixopCanon {α : Type} : ∀ (tree : Mixfix.t value) (pattern : Mixfix.t α),
    Mixfix.eq_mixop (canonMixfix tree) pattern = Mixfix.eq_mixop tree pattern
  | tree, pattern => by
    rcases tree with v | a | ⟨l,m,r⟩ | ⟨l,a,r⟩ | ts <;>
    rcases pattern with v' | a' | ⟨l',m',r'⟩ | ⟨l',a',r'⟩ | ts' <;>
      simp only [canonMixfix, Mixfix.eq_mixop, Mixfix.eq, mkPhrase]
    · simpa only [Mixfix.eq_mixop] using
        congrArg (fun b => Atom.eq l.it l'.it && b && Atom.eq r.it r'.it)
          (mixopCanon m m')
    · have hl := mixopCanon l l'
      have hr := mixopCanon r r'
      simp only [Mixfix.eq_mixop] at hl hr
      rw [hl, hr]
    · exact mixopsCanon ts ts'
private theorem mixopsCanon {α : Type} : ∀ (trees : List (Mixfix.t value))
    (patterns : List (Mixfix.t α)),
    Mixfix.eq.eqs (fun _ _ => true) (canonMixfixes trees) patterns =
      Mixfix.eq.eqs (fun _ _ => true) trees patterns
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, p :: ps => by
    simp only [canonMixfixes, Mixfix.eq.eqs]
    rw [show Mixfix.eq (fun _ _ => true) (canonMixfix t) p =
      Mixfix.eq (fun _ _ => true) t p from mixopCanon t p, mixopsCanon ts ps]
end

private theorem canonsAppend (xs ys : List value) : canons (xs ++ ys) = canons xs ++ canons ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, canons, ih]

mutual
private theorem argsCanon : ∀ (tree : Mixfix.t value),
    Mixfix.args (canonMixfix tree) = canons (Mixfix.args tree)
  | .Arg _ => by simp only [canonMixfix, Mixfix.args, canons]
  | .Atom _ => by simp only [canonMixfix, Mixfix.args, canons]
  | .Brack _ tree _ => by simpa only [canonMixfix, Mixfix.args] using argsCanon tree
  | .Infix left _ right => by
    simp only [canonMixfix, Mixfix.args, canonsAppend, argsCanon left, argsCanon right]
  | .Seq trees => by simpa only [canonMixfix, Mixfix.args] using argsCanons trees
private theorem argsCanons : ∀ (trees : List (Mixfix.t value)),
    (canonMixfixes trees).flatMap Mixfix.args = canons (trees.flatMap Mixfix.args)
  | [] => rfl
  | tree :: trees => by
    simp only [canonMixfixes, List.flatMap_cons, canonsAppend, argsCanon tree, argsCanons trees]
end

private theorem canonsLength (vs : List value) : (canons vs).length = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [canons, List.length_cons, ih]

/-- Source grammar validity is insensitive to canonical value observations when externs are. -/
theorem Valid.ofCanon {spec externalDomain}
    (externs : ∀ name v w, canon v = canon w → externalDomain name v → externalDomain name w)
    {type v} (valid : Valid spec externalDomain type v) (w : value)
    (same : canon v = canon w) : Valid spec externalDomain type w := by
  induction valid using Valid.rec
    (motive_2 := fun types vs _ => ∀ ws, canons vs = canons ws →
      Values spec externalDomain types ws) generalizing w with
  | bool v b shape => exact .bool w b (shapeBool shape same)
  | nat v n shape => exact .nat w n (shapeNat shape same)
  | int v n shape => exact .int w n (shapeInt shape same)
  | text v s shape => exact .text w s (shapeText shape same)
  | list element v values shape elements ih =>
    obtain ⟨ws, shape, equal⟩ := shapeList shape same
    have lengths : values.length = ws.length := by
      have := congrArg List.length equal
      simpa only [canonsLength] using this
    exact .list element w ws shape (lengths ▸ ih ws equal)
  | none element v shape => exact .none element w (shapeNone shape same)
  | some element v inner shape payload ih =>
    obtain ⟨next, shape, equal⟩ := shapeSome shape same
    exact .some element w next shape (ih next equal)
  | tuple types v values shape elements ih =>
    obtain ⟨ws, shape, equal⟩ := shapeTuple shape same
    exact .tuple types w ws shape (ih ws equal)
  | «alias» name arguments parameters definition instantiated v declared fields payload ih =>
    exact .alias name arguments parameters definition instantiated w declared fields
      (ih w same)
  | record name arguments parameters sourceFields instantiated v valueFields declared
      shape labels fields payload ih =>
    obtain ⟨fs, shape, equal⟩ := shapeRecord shape same
    obtain ⟨labelsEq, valuesEq⟩ := recordFields equal
    exact .record name arguments parameters sourceFields instantiated w fs declared shape
      (recordLabels labels labelsEq) fields (ih _ valuesEq)
  | variant name arguments parameters cases constructor instantiated v tree declared
      member shape matching fields payload ih =>
    obtain ⟨next, shape, equal⟩ := shapeVariant shape same
    have matched : Mixfix.eq_mixop next constructor.nottyp.it = true := by
      rw [← mixopCanon next, ← equal, mixopCanon tree]
      exact matching
    have valuesEq := congrArg Mixfix.args equal
    rw [argsCanon tree, argsCanon next] at valuesEq
    exact .variant name arguments parameters cases constructor instantiated w next declared
      member shape matched fields (ih _ valuesEq)
  | external name v declared payload =>
    exact .external name w declared (externs name.it v w same payload)
  | nil =>
    rename_i ws same
    cases ws <;> simp_all [canons]
    exact .nil
  | cons type v types values head tail ihHead ihTail =>
    rename_i ws same
    cases ws with
    | nil => simp [canons] at same
    | cons w ws =>
      simp only [canons, List.cons.injEq] at same
      exact .cons type w types ws (ihHead w same.1) (ihTail ws same.2)

/-- Canonically equal positional field lists preserve every independent source domain. -/
theorem Values.ofCanons {spec externalDomain}
    (externs : ∀ name v w, canon v = canon w → externalDomain name v → externalDomain name w)
    {types vs} (valid : Values spec externalDomain types vs) (ws : List value)
    (same : canons vs = canons ws) : Values spec externalDomain types ws := by
  induction vs generalizing types ws with
  | nil => cases valid; cases ws <;> simp_all [canons]; exact .nil
  | cons v vs ih =>
    cases valid with
    | cons type v types values head tail =>
      cases ws with
      | nil => simp [canons] at same
      | cons w ws =>
        simp only [canons, List.cons.injEq] at same
        exact .cons type w types ws (head.ofCanon externs w same.1)
          (ih tail ws same.2)

/-- info: 'P4SpecTec.Refine.Representation.Source.Valid.ofCanon' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Valid.ofCanon
#audit_axioms Valid.ofCanon
/-- info: 'P4SpecTec.Refine.Representation.Source.Values.ofCanons' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Values.ofCanons
#audit_axioms Values.ofCanons

/-- Opaque source membership accepts every canonically related extern payload. -/
theorem externDomainCanonical (name : String) (v w : value) (same : canon v = canon w)
    (valid : externDomain name v) : externDomain name w := by
  obtain ⟨payload, shape⟩ := valid
  cases hw : w.it <;> try (rename_i inner; cases inner)
  all_goals simp_all [externDomain, Shape.extern, canon, canon']

/-- info: 'P4SpecTec.Refine.Representation.Source.externDomainCanonical' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externDomainCanonical
#audit_axioms externDomainCanonical

/-- The declared source domain is invariant under canonical value equality. -/
theorem Valid.canonIff {spec type v w} (same : canon v = canon w) :
    Valid spec externDomain type v ↔ Valid spec externDomain type w :=
  ⟨fun valid => valid.ofCanon externDomainCanonical w same,
   fun valid => valid.ofCanon externDomainCanonical v same.symm⟩

/-- info: 'P4SpecTec.Refine.Representation.Source.Valid.canonIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Valid.canonIff
#audit_axioms Valid.canonIff

end P4SpecTec.Refine.Representation.Source

namespace P4SpecTec.Refine.Representation
open P4SpecTec.Prelude

/-- An admitted producer result transfers source validity to its related reference value. -/
theorem Codec.sourceOfRelated {α : Type} [ToValue α] [OfValue α]
    {spec type} {admitted : α → Prop}
    (contract : Codec (Source.Valid spec Source.externDomain type) admitted)
    {v : Lang.Il.value} {x : α} (accepted : admitted x) (related : Rel v x) :
    Source.Valid spec Source.externDomain type v :=
  (Source.Valid.canonIff related).mpr (contract.encodingValid x accepted)

/-- info: 'P4SpecTec.Refine.Representation.Codec.sourceOfRelated' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Codec.sourceOfRelated
#audit_axioms Codec.sourceOfRelated

end P4SpecTec.Refine.Representation
