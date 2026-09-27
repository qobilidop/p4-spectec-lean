import P4SpecTec.Lang.Al.Ast
import P4SpecTec.Refine.Representation

/-!
Finite source-grammar derivations from actual AL type declarations. The grammar
uses source constructor signatures and strict value tags, independently of generated
carriers and decoding. Relational substitution has no syntactic-depth cutoff.
Function and record shapes need separate contracts; this first fragment covers
primitive, list, optional, tuple, alias and variant declarations.
-/

namespace P4SpecTec.Refine.Representation.Source

open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Util.Source

/-- A finite syntactic type-parameter substitution, without decoder or fuel premises. -/
inductive Substitutes (bindings : List (String × typ')) : typ' → typ' → Prop where
  /-- Boolean types have no substitutable children. -/
  | bool : Substitutes bindings .BoolT .BoolT
  /-- Numeric types preserve their declared tag. -/
  | num (kind) : Substitutes bindings (.NumT kind) (.NumT kind)
  /-- Byte text has no substitutable children. -/
  | text : Substitutes bindings .TextT .TextT
  /-- A declared parameter is replaced only without higher-order arguments. -/
  | bound (name : id) (replacement : typ')
      (found : bindings.lookup name.it = some replacement) :
      Substitutes bindings (.VarT name []) replacement
  /-- Unbound named constructors retain their head and instantiate every argument. -/
  | named (name : id) (args instantiated : List typ)
      (unbound : bindings.lookup name.it = none)
      (arguments : List.Forall₂ (fun a b => Substitutes bindings a.it b.it) args instantiated) :
      Substitutes bindings (.VarT name args) (.VarT name instantiated)
  /-- Tuple components are instantiated positionally, with the exact source arity. -/
  | tuple (args instantiated : List typ)
      (arguments : List.Forall₂ (fun a b => Substitutes bindings a.it b.it) args instantiated) :
      Substitutes bindings (.TupleT args) (.TupleT instantiated)
  /-- Iteration preserves its source kind and instantiates its element. -/
  | iter (element instantiated : typ) (kind : iter)
      (argument : Substitutes bindings element.it instantiated.it) :
      Substitutes bindings (.IterT element kind) (.IterT instantiated kind)

/-- Select the first type-namespace declaration of a source name in the specification. -/
def declaration (spec : Lang.Al.spec) (name : String) : Option Lang.Al.def :=
  spec.find? (fun d => match d.it with
    | .TypD tid .. | .ExternTypD tid .. => tid.it == name
    | _ => false)

/-- Read a type body without constraining declaration metadata to value metadata. -/
def body (spec : Lang.Al.spec) (name : String) : Option (List tparam × deftyp') := do
  let d ← declaration spec name
  let .TypD _ parameters definition _ := d.it | none
  pure (parameters, definition.it)

/-- Identify an actual external-type declaration, ignoring source locations. -/
def external (spec : Lang.Al.spec) (name : String) : Bool :=
  match declaration spec name with
  | some d => match d.it with | .ExternTypD .. => true | _ => false
  | none => false

/-- Instantiate all positional constructor fields using the declared parameter binding. -/
def instantiatedFields (parameters : List tparam) (arguments : List typ)
    (fields instantiated : List typ) : Prop :=
  parameters.length = arguments.length ∧
    List.Forall₂
      (fun a b => Substitutes
        (((parameters.map (·.it)).zip (arguments.map (·.it))).reverse) a.it b.it)
      fields instantiated

mutual

/-- A finite derivation of a source value from its actual declared grammar.
Opaque external source domains are supplied independently; runtime extensions
are not implicit alternatives of this predicate. -/
inductive Valid (spec : Lang.Al.spec) (externalDomain : String → value → Prop) :
    typ' → value → Prop where
  /-- Strict source Boolean constructor. -/
  | bool (v : value) (b : Bool) (shape : v.it = .BoolV b) : Valid spec externalDomain .BoolT v
  /-- Strict natural tag; integer-tag membership is insufficient for source naturals. -/
  | nat (v : value) (n : Nat) (shape : v.it = .NumV (.Nat n)) :
      Valid spec externalDomain (.NumT .NatT) v
  /-- Strict integer tag; source coercion is a separate producer obligation. -/
  | int (v : value) (n : Int) (shape : v.it = .NumV (.Int n)) :
      Valid spec externalDomain (.NumT .IntT) v
  /-- Source byte-text constructor. -/
  | text (v : value) (text : ByteText) (shape : v.it = .TextV text) :
      Valid spec externalDomain .TextT v
  /-- Lists preserve every element, its order and multiplicity. -/
  | list (element : typ) (v : value) (values : List value) (shape : v.it = .ListV values)
      (elements : Values spec externalDomain (List.replicate values.length element) values) :
      Valid spec externalDomain (.IterT element .List) v
  /-- Absent source options use OptV, rather than an empty list. -/
  | none (element : typ) (v : value) (shape : v.it = .OptV none) :
      Valid spec externalDomain (.IterT element .Opt) v
  /-- Present options recursively preserve source validity. -/
  | some (element : typ) (v inner : value) (shape : v.it = .OptV (some inner))
      (payload : Valid spec externalDomain element.it inner) :
      Valid spec externalDomain (.IterT element .Opt) v
  /-- Tuples use exact positional source arities, without flattening hidden products. -/
  | tuple (types : List typ) (v : value) (values : List value)
      (shape : v.it = .TupleV values) (elements : Values spec externalDomain types values) :
      Valid spec externalDomain (.TupleT types) v
  /-- A plain declaration is interpreted through syntactic parameter instantiation. -/
  | alias (name : id) (arguments : List typ) (parameters : List tparam)
      (definition instantiated : typ) (v : value)
      (declared : body spec name.it = some (parameters, .PlainT definition))
      (fields : instantiatedFields parameters arguments [definition] [instantiated])
      (payload : Valid spec externalDomain instantiated.it v) :
      Valid spec externalDomain (.VarT name arguments) v
  /-- A variant is selected from the quoted source cases, with all its fields valid. -/
  | variant (name : id) (arguments : List typ) (parameters : List tparam)
      (cases : List typcase) (constructor : typcase) (instantiated : List typ)
      (v : value) (tree : Mixfix.t value)
      (declared : body spec name.it = some (parameters, .VariantT cases))
      (member : constructor ∈ cases) (shape : v.it = .CaseV tree)
      (mixopMatches : Mixfix.eq_mixop tree constructor.nottyp.it = true)
      (fields : instantiatedFields parameters arguments
        (Mixfix.args constructor.nottyp.it) instantiated)
      (payload : Values spec externalDomain instantiated (Mixfix.args tree)) :
      Valid spec externalDomain (.VarT name arguments) v
  /-- External declarations require their independently specified source domain. -/
  | external (name : id) (v : value)
      (declared : external spec name.it = true)
      (payload : externalDomain name.it v) : Valid spec externalDomain (.VarT name []) v

/-- Positional source validity for a finite field list of arbitrary length. -/
inductive Values (spec : Lang.Al.spec) (externalDomain : String → value → Prop) :
    List typ → List value → Prop where
  /-- No fields require no values. -/
  | nil : Values spec externalDomain [] []
  /-- Every head and tail are independently source-valid. -/
  | cons (type : typ) (v : value) (types : List typ) (values : List value)
      (head : Valid spec externalDomain type.it v)
      (tail : Values spec externalDomain types values) :
      Values spec externalDomain (type :: types) (v :: values)

end

/-- Positional source validity retains exact arity. -/
theorem Values.length {spec : Lang.Al.spec} {externalDomain : String → value → Prop}
    {types : List typ} {values : List value} (valid : Values spec externalDomain types values) :
    types.length = values.length := by
  induction values generalizing types with
  | nil => cases valid; rfl
  | cons v values ih =>
    cases valid with
    | cons type v types values head tail => exact congrArg Nat.succ (ih tail)

/-- info: 'P4SpecTec.Refine.Representation.Source.Values.length' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Values.length
#audit_axioms Values.length

/-- The atom constructors in a quoted nullary variant declaration.
Non-atomic constructors are deliberately absent; callers claiming an entire
source family must separately establish that every declared constructor is atomic. -/
def atomKinds (d : Lang.Al.def) : List Atom.t :=
  match d.it with
  | .TypD _ [] definition _ => match definition.it with
    | .VariantT cases => cases.filterMap (fun c => match c.nottyp.it with
        | .Atom a => some a.it | _ => none)
    | _ => []
  | _ => []

/-- The independently quoted atomic constructor grammar, allowing arbitrary metadata. -/
def atomVariant (d : Lang.Al.def) (v : value) : Prop :=
  ∃ a : Mixfix.atom, v.it = .CaseV (.Atom a) ∧ a.it ∈ atomKinds d

mutual

/-- Matching source notation preserves the number of constructor fields. -/
theorem mixopArity {α β : Type} : ∀ (a : Mixfix.t α) (b : Mixfix.t β),
    Mixfix.eq_mixop a b = true → (Mixfix.args a).length = (Mixfix.args b).length
  | a, b => by
    rcases a with a | a | ⟨la, ma, ra⟩ | ⟨la, aa, ra⟩ | a <;>
    rcases b with b | b | ⟨lb, mb, rb⟩ | ⟨lb, ab, rb⟩ | b <;>
      first
      | (simp [Mixfix.eq_mixop, Mixfix.eq, Mixfix.args]; done)
      | (intro h; simp only [Mixfix.eq_mixop, Mixfix.eq, Bool.and_eq_true] at h
         simpa only [Mixfix.args] using mixopArity ma mb h.1.2)
      | (intro h; simp only [Mixfix.eq_mixop, Mixfix.eq, Bool.and_eq_true] at h
         simp only [Mixfix.args, List.length_append]
         rw [mixopArity la lb h.1.2, mixopArity ra rb h.2])
      | (simpa only [Mixfix.eq_mixop, Mixfix.eq, Mixfix.args] using mixopsArity a b)


/-- Matching source notation sequences preserve total field arity. -/
theorem mixopsArity {α β : Type} : ∀ (a : List (Mixfix.t α)) (b : List (Mixfix.t β)),
    Mixfix.eq.eqs (fun _ _ => true) a b = true →
      (a.flatMap Mixfix.args).length = (b.flatMap Mixfix.args).length
  | [], [] => by simp
  | [], _ :: _ => by simp [Mixfix.eq.eqs]
  | _ :: _, [] => by simp [Mixfix.eq.eqs]
  | a :: as, b :: bs => by
    intro h
    simp only [Mixfix.eq.eqs, Bool.and_eq_true] at h
    simp only [List.flatMap_cons, List.length_append]
    rw [mixopArity a b h.1, mixopsArity as bs h.2]

end

/-- info: 'P4SpecTec.Refine.Representation.Source.mixopArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixopArity
#audit_axioms mixopArity
/-- info: 'P4SpecTec.Refine.Representation.Source.mixopsArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixopsArity
#audit_axioms mixopsArity

private theorem canonsAppend (a b : List value) : canons (a ++ b) = canons a ++ canons b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append, canons, ih]

private theorem canonsLength (a : List value) : (canons a).length = a.length := by
  induction a with
  | nil => rfl
  | cons a as ih => simp only [canons, List.length_cons, ih]

private theorem atomEqCanonical (a b : Mixfix.atom) (h : Atom.eq a.it b.it = true) :
    mkPhrase a.it = mkPhrase b.it := by
  apply atom_phrase_eq.mpr
  simpa [Atom.eq, Atom.compare_eq_iff] using h

mutual

/-- Source notation and related positional fields determine a canonical constructor tree. -/
theorem reconstructMixfix : ∀ (a b : Mixfix.t value), Mixfix.eq_mixop a b = true →
    canons (Mixfix.args a) = canons (Mixfix.args b) → canonMixfix a = canonMixfix b
  | a, b => by
    rcases a with a | a | ⟨la, ma, ra⟩ | ⟨la, aa, ra⟩ | a <;>
    rcases b with b | b | ⟨lb, mb, rb⟩ | ⟨lb, ab, rb⟩ | b <;>
      first
      | (simp [Mixfix.eq_mixop, Mixfix.eq, Mixfix.args, canons, canonMixfix]; done)
      | (intro hm hv; simp only [Mixfix.eq_mixop, Mixfix.eq] at hm
         simpa only [canonMixfix] using congrArg Mixfix.t.Atom (atomEqCanonical a b hm))
      | (intro hm hv; simp only [Mixfix.eq_mixop, Mixfix.eq, Bool.and_eq_true] at hm
         simp only [Mixfix.args] at hv
         simp only [canonMixfix]
         rw [atomEqCanonical la lb hm.1.1, atomEqCanonical ra rb hm.2,
           reconstructMixfix ma mb hm.1.2 hv])
      | (intro hm hv
         have arity := mixopArity la lb
         simp only [Mixfix.eq_mixop, Mixfix.eq, Bool.and_eq_true] at hm
         have parts := List.append_inj
           (show canons (Mixfix.args la) ++ canons (Mixfix.args ra) =
             canons (Mixfix.args lb) ++ canons (Mixfix.args rb) from
             by simpa only [Mixfix.args, canonsAppend] using hv)
           (by simpa only [canonsLength] using arity hm.1.2)
         simp only [canonMixfix]
         rw [atomEqCanonical aa ab hm.1.1,
           reconstructMixfix la lb hm.1.2 parts.1,
           reconstructMixfix ra rb hm.2 parts.2])
      | (intro hm hv; simp only [Mixfix.args] at hv; simp only [canonMixfix]
         exact congrArg Mixfix.t.Seq (reconstructMixfixes a b hm hv))

/-- The sequence form of positional source-constructor reconstruction. -/
theorem reconstructMixfixes : ∀ (a b : List (Mixfix.t value)),
    Mixfix.eq.eqs (fun _ _ => true) a b = true →
    canons (a.flatMap Mixfix.args) = canons (b.flatMap Mixfix.args) →
      canonMixfixes a = canonMixfixes b
  | [], [] => by simp [canonMixfixes]
  | [], _ :: _ => by simp [Mixfix.eq.eqs]
  | _ :: _, [] => by simp [Mixfix.eq.eqs]
  | a :: as, b :: bs => by
    intro hm hv
    simp only [Mixfix.eq.eqs, Bool.and_eq_true] at hm
    simp only [List.flatMap_cons, canonsAppend] at hv
    have parts := List.append_inj hv (by
      simpa only [canonsLength] using mixopArity a b hm.1)
    simp only [canonMixfixes]
    rw [reconstructMixfix a b hm.1 parts.1, reconstructMixfixes as bs hm.2 parts.2]

end

/-- info: 'P4SpecTec.Refine.Representation.Source.reconstructMixfix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reconstructMixfix
#audit_axioms reconstructMixfix
/-- info: 'P4SpecTec.Refine.Representation.Source.reconstructMixfixes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reconstructMixfixes
#audit_axioms reconstructMixfixes
end P4SpecTec.Refine.Representation.Source
