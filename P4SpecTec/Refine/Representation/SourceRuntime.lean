import P4SpecTec.Refine.Representation.SourceExtern

/-!
Runtime profiles of the declared grammar. A runtime profile admits, besides the source
constructors, a raw extern value at configured declared types (`runtimeDomain`). Source
validity is a special case (`Valid.mono`); conversely, a value of a type whose declared
closure never reaches a runtime type is source valid (`Valid.ofRuntime`), checked once per
specification by `closedCheck`.
This is our own proof support, not an upstream mirror.
-/

namespace P4SpecTec.Refine.Representation.Source

open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Prelude

/-- Every opaque and runtime-only value of `d` is also admitted by `e`. -/
def Domain.Le (d e : Domain) : Prop :=
  (∀ name v, d.external name v → e.external name v) ∧
    (∀ name v, d.runtime name v → e.runtime name v)

/-- Validity is monotone in the domain's opaque and runtime-only parts. -/
theorem Valid.mono {spec : Lang.Al.spec} {d e : Domain} (le : Domain.Le d e) {type : typ'}
    {v : value} (valid : Valid spec d type v) : Valid spec e type v := by
  induction valid using Valid.rec (motive_2 := fun types vs _ => Values spec e types vs) with
  | bool v b shape => exact .bool v b shape
  | nat v n shape => exact .nat v n shape
  | int v n shape => exact .int v n shape
  | text v s shape => exact .text v s shape
  | list element v values shape elements ih => exact .list element v values shape ih
  | none element v shape => exact .none element v shape
  | some element v inner shape payload ih => exact .some element v inner shape ih
  | tuple types v values shape elements ih => exact .tuple types v values shape ih
  | «alias» name arguments parameters definition instantiated v declared fields payload ih =>
    exact .alias name arguments parameters definition instantiated v declared fields ih
  | record name arguments parameters sourceFields instantiated v valueFields declared
      shape labels fields payload ih =>
    exact .record name arguments parameters sourceFields instantiated v valueFields declared
      shape labels fields ih
  | variant name arguments parameters cases constructor instantiated v tree declared
      member shape matching fields payload ih =>
    exact .variant name arguments parameters cases constructor instantiated v tree declared
      member shape matching fields ih
  | external name v declared payload => exact .external name v declared (le.1 _ _ payload)
  | runtime name arguments v payload => exact .runtime name arguments v (le.2 _ _ payload)
  | nil => exact .nil
  | cons type v types values head tail ihHead ihTail =>
    exact .cons type v types values ihHead ihTail

/-- info: 'P4SpecTec.Refine.Representation.Source.Valid.mono' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Valid.mono
#audit_axioms Valid.mono

/-- The source domain is included in every runtime profile. -/
theorem externDomainLe (types : List String) : Domain.Le externDomain (runtimeDomain types) :=
  ⟨fun _ _ payload => payload, fun name v payload => absurd payload (externDomainNoRuntime name v)⟩

/-- info: 'P4SpecTec.Refine.Representation.Source.externDomainLe' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externDomainLe
#audit_axioms externDomainLe

/-- A raw extern at a runtime type is a runtime-only alternative of its profile. -/
theorem runtimeDomainExtern {types : List String} {name : String} (member : name ∈ types)
    {v : value} {j : Lean.Json} (shape : v.it = .ExternV j) :
    (runtimeDomain types).runtime name v :=
  ⟨member, j, shape⟩

/-- info: 'P4SpecTec.Refine.Representation.Source.runtimeDomainExtern' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtimeDomainExtern
#audit_axioms runtimeDomainExtern

/-- A runtime-only alternative of a runtime profile is a raw extern at a runtime type. -/
theorem runtimeDomainPayload {types : List String} {name : String} {v : value}
    (payload : (runtimeDomain types).runtime name v) :
    name ∈ types ∧ ∃ j, v.it = .ExternV j :=
  payload

/-- info: 'P4SpecTec.Refine.Representation.Source.runtimeDomainPayload' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtimeDomainPayload
#audit_axioms runtimeDomainPayload

/-- Every declared type name in a type phrase is in `names`; function types are excluded. -/
inductive NamesIn (names : List String) : typ' → Prop where
  /-- Booleans name no declaration. -/
  | bool : NamesIn names .BoolT
  /-- Numbers name no declaration. -/
  | num (kind) : NamesIn names (.NumT kind)
  /-- Byte text names no declaration. -/
  | text : NamesIn names .TextT
  /-- A named type and all its arguments. -/
  | var (name : id) (arguments : List typ) (member : name.it ∈ names)
      (payload : ∀ a ∈ arguments, NamesIn names a.it) : NamesIn names (.VarT name arguments)
  /-- Every tuple component. -/
  | tuple (types : List typ) (payload : ∀ t ∈ types, NamesIn names t.it) :
      NamesIn names (.TupleT types)
  /-- The iterated element. -/
  | iter (element : typ) (kind : iter) (payload : NamesIn names element.it) :
      NamesIn names (.IterT element kind)

/-- The field types a declared body mentions, in declaration order. -/
def bodyFields : deftyp' → List typ
  | .PlainT t => [t]
  | .StructT fields => fields.map (·.2)
  | .VariantT cases => cases.flatMap fun c => Mixfix.args c.nottyp.it

/-- The declared bodies of `names` mention only `names` and their own parameters, and the
domain adds no runtime-only alternative at any of them. -/
def ClosedAvoiding (spec : Lang.Al.spec) (domain : Domain) (names : List String) : Prop :=
  ∀ name ∈ names, Domain.SourceOnly domain name ∧
    ∀ parameters definition, body spec name = some (parameters, definition) →
      ∀ field ∈ bodyFields definition, NamesIn (names ++ parameters.map (·.it)) field.it

private theorem namesInWeaken {names names' : List String} (sub : ∀ n ∈ names, n ∈ names')
    {t : typ'} (h : NamesIn names t) : NamesIn names' t := by
  induction h with
  | bool => exact .bool
  | num kind => exact .num kind
  | text => exact .text
  | var name arguments member _ ih => exact .var name arguments (sub _ member) ih
  | tuple types _ ih => exact .tuple types ih
  | iter element kind _ ih => exact .iter element kind ih

/-- A key absent from an association list's lookup is not among its keys. -/
private theorem lookupNoneKey {bindings : List (String × typ')} {key : String}
    (absent : bindings.lookup key = none) : key ∉ bindings.map (·.1) := by
  induction bindings with
  | nil => simp
  | cons binding rest ih =>
    obtain ⟨k, t⟩ := binding
    simp only [List.lookup] at absent
    by_cases same : key = k
    · subst same; simp at absent
    · have : (key == k) = false := by simpa using same
      rw [this] at absent
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨same, ih absent⟩

/-- A found binding is one of the association list's replacements. -/
private theorem lookupSomeMem {bindings : List (String × typ')} {key : String} {t : typ'}
    (found : bindings.lookup key = some t) : (key, t) ∈ bindings := by
  induction bindings with
  | nil => simp at found
  | cons binding rest ih =>
    obtain ⟨k, u⟩ := binding
    simp only [List.lookup] at found
    by_cases same : key = k
    · subst same; simp at found; subst found; simp
    · have : (key == k) = false := by simpa using same
      rw [this] at found
      exact List.mem_cons_of_mem _ (ih found)

/-- Substitution by replacements naming only `names` removes the bound parameters. -/
theorem Substitutes.namesIn {names : List String} {bindings : List (String × typ')}
    (replacements : ∀ p ∈ bindings, NamesIn names p.2) {a b : typ'}
    (sub : Substitutes bindings a b) (h : NamesIn (names ++ bindings.map (·.1)) a) :
    NamesIn names b := by
  induction sub using Substitutes.rec
    (motive_2 := fun args instantiated _ =>
      (∀ a ∈ args, NamesIn (names ++ bindings.map (·.1)) a.it) →
        ∀ b ∈ instantiated, NamesIn names b.it) with
  | bool => exact .bool
  | num kind => exact .num kind
  | text => exact .text
  | bound name replacement found => exact replacements _ (lookupSomeMem found)
  | named name args instantiated unbound arguments ih =>
    cases h with
    | var _ _ member payload =>
      rcases List.mem_append.mp member with member | member
      · exact .var name instantiated member (ih payload)
      · exact absurd member (lookupNoneKey unbound)
  | tuple args instantiated arguments ih =>
    cases h with
    | tuple _ payload => exact .tuple instantiated (ih payload)
  | iter element instantiated kind argument ih =>
    cases h with
    | iter _ _ payload => exact .iter instantiated kind (ih payload)
  | nil _ _ member => cases member
  | cons _ _ ihHead ihTail all c member =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ihHead (all _ (by simp))
    · exact ihTail (fun x hx => all x (List.mem_cons_of_mem _ hx)) c member

/-- info: 'P4SpecTec.Refine.Representation.Source.Substitutes.namesIn' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Substitutes.namesIn
#audit_axioms Substitutes.namesIn

/-- Instantiated fields of a closed declaration name only closed types. -/
private theorem instantiatedNamesIn {names : List String} {parameters : List tparam}
    {arguments fields instantiated : List typ}
    (hargs : ∀ a ∈ arguments, NamesIn names a.it)
    (hfields : ∀ f ∈ fields, NamesIn (names ++ parameters.map (·.it)) f.it)
    (inst : instantiatedFields parameters arguments fields instantiated) :
    ∀ t ∈ instantiated, NamesIn names t.it := by
  obtain ⟨lengths, subs⟩ := inst
  let bindings := ((parameters.map (·.it)).zip (arguments.map (·.it))).reverse
  have keys : bindings.map (·.1) = (parameters.map (·.it)).reverse := by
    simp only [bindings, List.map_reverse]
    rw [List.map_fst_zip]
    simp [lengths]
  have replacements : ∀ p ∈ bindings, NamesIn names p.2 := by
    intro p member
    simp only [bindings, List.mem_reverse] at member
    have := List.of_mem_zip member
    obtain ⟨a, ha, eq⟩ := List.mem_map.mp this.2
    rw [← eq]; exact hargs a ha
  induction subs with
  | nil => intro t member; cases member
  | cons head tail ih =>
    rename_i f t fs ts
    intro u member
    rcases List.mem_cons.mp member with rfl | member
    · apply head.namesIn replacements
      apply namesInWeaken _ (hfields f (by simp))
      intro n hn
      rw [keys]
      simpa using hn
    · exact ih (fun g hg => hfields g (List.mem_cons_of_mem _ hg)) u member

/-- A value of a runtime profile whose type avoids every runtime type is source valid. -/
theorem Valid.ofRuntime {spec : Lang.Al.spec} {domain : Domain} {names : List String}
    (closed : ClosedAvoiding spec domain names)
    (externals : ∀ name v, domain.external name v → externDomain.external name v)
    {type : typ'} {v : value} (valid : Valid spec domain type v) (hn : NamesIn names type) :
    Valid spec externDomain type v := by
  revert hn
  induction valid using Valid.rec
    (motive_2 := fun types vs _ => (∀ t ∈ types, NamesIn names t.it) →
      Values spec externDomain types vs) with
  | bool v b shape => intro _; exact .bool v b shape
  | nat v n shape => intro _; exact .nat v n shape
  | int v n shape => intro _; exact .int v n shape
  | text v s shape => intro _; exact .text v s shape
  | list element v values shape elements ih =>
    intro hn
    cases hn with
    | iter _ _ payload =>
      exact .list element v values shape (ih fun t member => by
        rw [List.eq_of_mem_replicate member]; exact payload)
  | none element v shape => intro _; exact .none element v shape
  | some element v inner shape payload ih =>
    intro hn
    cases hn with
    | iter _ _ payload' => exact .some element v inner shape (ih payload')
  | tuple types v values shape elements ih =>
    intro hn
    cases hn with
    | tuple _ payload => exact .tuple types v values shape (ih payload)
  | «alias» name arguments parameters definition instantiated v declared fields payload ih =>
    intro hn
    cases hn with
    | var _ _ member hargs =>
      have hbody := (closed name.it member).2 parameters (.PlainT definition) declared
      exact .alias name arguments parameters definition instantiated v declared fields
        (ih (instantiatedNamesIn hargs hbody fields instantiated (by simp)))
  | record name arguments parameters sourceFields instantiated v valueFields declared
      shape labels fields payload ih =>
    intro hn
    cases hn with
    | var _ _ member hargs =>
      have hbody := (closed name.it member).2 parameters (.StructT sourceFields) declared
      exact .record name arguments parameters sourceFields instantiated v valueFields declared
        shape labels fields (ih (instantiatedNamesIn hargs hbody fields))
  | variant name arguments parameters cases constructor instantiated v tree declared
      member shape matching fields payload ih =>
    intro hn
    cases hn with
    | var _ _ named hargs =>
      have hbody := (closed name.it named).2 parameters (.VariantT cases) declared
      have hcase : ∀ f ∈ Mixfix.args constructor.nottyp.it,
          NamesIn (names ++ parameters.map (·.it)) f.it := fun f hf =>
        hbody f (List.mem_flatMap.mpr ⟨constructor, member, hf⟩)
      exact .variant name arguments parameters cases constructor instantiated v tree declared
        member shape matching fields (ih (instantiatedNamesIn hargs hcase fields))
  | external name v declared payload =>
    intro _; exact .external name v declared (externals _ _ payload)
  | runtime name arguments v payload =>
    intro hn
    cases hn with
    | var _ _ member _ => exact absurd payload ((closed name.it member).1 v)
  | nil _ => exact .nil
  | cons type v types values head tail ihHead ihTail all =>
    exact .cons type v types values (ihHead (all type (by simp)))
      (ihTail fun t member => all t (List.mem_cons_of_mem _ member))

/-- info: 'P4SpecTec.Refine.Representation.Source.Valid.ofRuntime' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Valid.ofRuntime
#audit_axioms Valid.ofRuntime

mutual

/-- Decide `NamesIn` by evaluation. -/
def namesInCheck (names : List String) : typ' → Bool
  | .BoolT | .NumT _ | .TextT => true
  | .VarT name arguments => names.contains name.it && namesInChecks names arguments
  | .TupleT types => namesInChecks names types
  | .IterT element _ => namesInCheck names element.it
  | .FuncT .. => false

/-- Decide `NamesIn` for every type of a list by evaluation. -/
def namesInChecks (names : List String) : List typ → Bool
  | [] => true
  | t :: ts => namesInCheck names t.it && namesInChecks names ts

end

mutual

/-- The evaluated check is sound. -/
theorem namesInCheckSound (names : List String) :
    ∀ t : typ', namesInCheck names t = true → NamesIn names t
  | .BoolT, _ => .bool
  | .NumT kind, _ => .num kind
  | .TextT, _ => .text
  | .VarT name arguments, h => by
    simp only [namesInCheck, Bool.and_eq_true, List.contains_iff_mem] at h
    exact .var name arguments h.1 (fun a ha => namesInChecksSound names arguments h.2 a ha)
  | .TupleT types, h => .tuple types (fun t ht => namesInChecksSound names types h t ht)
  | .IterT element kind, h => .iter element kind (namesInCheckSound names element.it h)
  | .FuncT .., h => by simp [namesInCheck] at h

/-- The evaluated list check is sound. -/
theorem namesInChecksSound (names : List String) :
    ∀ ts : List typ, namesInChecks names ts = true → ∀ t ∈ ts, NamesIn names t.it
  | [], _, _, member => by cases member
  | t :: ts, h, u, member => by
    have both : namesInCheck names t.it = true ∧ namesInChecks names ts = true := by
      simpa only [namesInChecks, Bool.and_eq_true] using h
    have head := namesInCheckSound names t.it both.1
    have tail := namesInChecksSound names ts both.2
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact tail u member

end

/-- info: 'P4SpecTec.Refine.Representation.Source.namesInCheckSound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms namesInCheckSound
#audit_axioms namesInCheckSound

mutual

/-- `Mixfix.args` by structural recursion, so that it reduces by evaluation. -/
def mixfixArgs {α : Type} : Mixfix.t α → List α
  | .Arg a => [a]
  | .Atom _ => []
  | .Brack _ m _ => mixfixArgs m
  | .Infix l _ r => mixfixArgs l ++ mixfixArgs r
  | .Seq ms => mixfixArgsList ms

/-- The arguments of a notation sequence, by structural recursion. -/
def mixfixArgsList {α : Type} : List (Mixfix.t α) → List α
  | [] => []
  | m :: ms => mixfixArgs m ++ mixfixArgsList ms

end

mutual

/-- The structural arguments are the notation's arguments. -/
theorem mixfixArgsEq {α : Type} : ∀ m : Mixfix.t α, mixfixArgs m = Mixfix.args m
  | .Arg _ => by simp only [mixfixArgs, Mixfix.args]
  | .Atom _ => by simp only [mixfixArgs, Mixfix.args]
  | .Brack _ m _ => by simp only [mixfixArgs, Mixfix.args, mixfixArgsEq m]
  | .Infix l _ r => by simp only [mixfixArgs, Mixfix.args, mixfixArgsEq l, mixfixArgsEq r]
  | .Seq ms => by simp only [mixfixArgs, Mixfix.args, mixfixArgsListEq ms]

/-- The structural sequence arguments are the flattened notation arguments. -/
theorem mixfixArgsListEq {α : Type} : ∀ ms : List (Mixfix.t α),
    mixfixArgsList ms = ms.flatMap Mixfix.args
  | [] => rfl
  | m :: ms => by
    simp only [mixfixArgsList, List.flatMap_cons, mixfixArgsEq m, mixfixArgsListEq ms]

end

/-- `bodyFields` by structural recursion, so that it reduces by evaluation. -/
def bodyFieldsCheck : deftyp' → List typ
  | .PlainT t => [t]
  | .StructT fields => fields.map (·.2)
  | .VariantT cases => cases.flatMap fun c => mixfixArgs c.nottyp.it

private theorem bodyFieldsCheckEq (d : deftyp') : bodyFieldsCheck d = bodyFields d := by
  cases d <;> simp [bodyFieldsCheck, bodyFields, mixfixArgsEq]

/-- Decide `ClosedAvoiding` for a runtime profile by evaluation. -/
def closedCheck (spec : Lang.Al.spec) (types names : List String) : Bool :=
  names.all fun name => !types.contains name &&
    match body spec name with
    | some (parameters, definition) =>
      (bodyFieldsCheck definition).all fun field =>
        namesInCheck (names ++ parameters.map (·.it)) field.it
    | none => true

/-- Decide a closure check (`namesInCheck`, `closedCheck`) by kernel evaluation. A single
token, so that generated proofs survive line wrapping. -/
macro "closure_check" : tactic => `(tactic| decide +kernel)

/-- The evaluated closure check is sound. -/
theorem closedCheckSound {spec : Lang.Al.spec} {types names : List String}
    (h : closedCheck spec types names = true) :
    ClosedAvoiding spec (runtimeDomain types) names := by
  intro name member
  have entry := List.all_eq_true.mp h name member
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at entry
  refine ⟨fun v admitted => ?_, fun parameters definition declared field fieldMember => ?_⟩
  · simp only [runtimeDomain] at admitted
    have present : types.contains name = true := List.contains_iff_mem.mpr admitted.1
    rw [entry.1] at present
    cases present
  · have fields := entry.2
    simp only [declared, bodyFieldsCheckEq] at fields
    exact namesInCheckSound _ _ (List.all_eq_true.mp fields field fieldMember)

/-- info: 'P4SpecTec.Refine.Representation.Source.closedCheckSound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms closedCheckSound
#audit_axioms closedCheckSound

/-- A type whose closure avoids the runtime types has the same values in the runtime profile. -/
theorem Valid.runtimeIff {spec : Lang.Al.spec} {types names : List String}
    (closed : ClosedAvoiding spec (runtimeDomain types) names) {type : typ'}
    (hn : NamesIn names type) (v : value) :
    Valid spec externDomain type v ↔ Valid spec (runtimeDomain types) type v :=
  ⟨fun valid => valid.mono (externDomainLe types),
   fun valid => valid.ofRuntime closed (fun _ _ payload => payload) hn⟩

/-- info: 'P4SpecTec.Refine.Representation.Source.Valid.runtimeIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Valid.runtimeIff
#audit_axioms Valid.runtimeIff

/-- A source codec of a type whose closure avoids the runtime types is its runtime codec. -/
theorem Codec.toRuntime {α : Type} [ToValue α] [OfValue α] {spec : Lang.Al.spec}
    {types names : List String} (closed : ClosedAvoiding spec (runtimeDomain types) names)
    {type : typ'} (hn : NamesIn names type) {admitted : α → Prop}
    (contract : Codec (Valid spec externDomain type) admitted) :
    Codec (Valid spec (runtimeDomain types) type) admitted :=
  Codec.sourceIff (fun v => Valid.runtimeIff closed hn v) contract

/-- info: 'P4SpecTec.Refine.Representation.Source.Codec.toRuntime' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Codec.toRuntime
#audit_axioms Codec.toRuntime

end P4SpecTec.Refine.Representation.Source
