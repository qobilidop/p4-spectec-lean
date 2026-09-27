import P4SpecTec.Codegen.Certificates.Producer
import P4SpecTec.Codegen.Certificates.ProducerContext

/-!
Source-role producer proofs for checked context insertion and list-tail exit recipes.
The classifier binds all paths, ordered clauses, record fields and map representations;
this renderer supplies separately audited preservation over independent source domains.
-/

namespace P4SpecTec.Codegen.ProducerContextProof

open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Codegen.Types P4SpecTec.Refine
open ProducerContexts

private def template (source : String) (roles : List (String × String)) :
    Except String String := do
  let pieces := source.splitOn "@@"
  unless pieces.length % 2 == 1 do throw "context proof template has an open role"
  let output ← pieces.zipIdx.mapM fun (piece, index) => do
    if index % 2 == 0 then pure piece else
      let some (_, value) := roles.find? (·.1 == piece)
        | throw s!"context proof template lacks role {piece}"
      pure value
  pure (String.join output)

private def insertionTemplate : String :=
  "private def frameValid (keys : @@KEY_TYPE@@ → Prop) " ++
  "(valid : @@VALUE_TYPE@@ → Prop) : @@FRAME_TYPE@@ → Prop :=\n" ++
  "  @@SET@@.admitted (@@PAIR@@.admitted keys valid)\n" ++
  "\nprivate def contextValid (keys : @@KEY_TYPE@@ → Prop) (valid : @@VALUE_TYPE@@ → Prop)\n" ++
  "    (other : @@OTHER_TYPE@@)\n" ++
  "    (ctx : @@CONTEXT_TYPE@@) : Prop :=\n" ++
  "  other @@OTHER_ACCESS@@ ∧\n" ++
  "  frameValid keys valid @@GLOBAL_ACCESS@@ ∧ frameValid keys valid @@BLOCK_ACCESS@@ ∧\n" ++
  "  ∀ frame ∈ @@LOCAL_ACCESS@@, frameValid keys valid frame\n" ++
  "\n" ++
  "private theorem addMapValid (keys : @@KEY_TYPE@@ → Prop) " ++
  "(valid : @@VALUE_TYPE@@ → Prop) (frame : @@FRAME_TYPE@@)\n" ++
  "    (key : @@KEY_TYPE@@) (value : @@VALUE_TYPE@@) (hf : frameValid keys valid frame)\n" ++
  "    (hk : keys key) (hv : valid value) :\n" ++
  "    Produces (frameValid keys valid) (ExceptT.mk (@@INSERTION@@ frame key value)) := by\n" ++
  "  cases frame with\n" ++
  "  | @@SET_CTOR@@ pairs =>\n" ++
  "    intro result run\n" ++
  "    have same : result = _ := (Except.ok.inj (Option.some.inj run)).symm\n" ++
  "    subst result\n" ++
  "    dsimp [frameValid, @@SET@@.admitted, @@PAIR@@.admitted] at *\n" ++
  "    intro pair member\n" ++
  "    obtain ⟨⟨k, v⟩, belongs, rfl⟩ := List.mem_map.mp member\n" ++
  "    have all : ∀ pair ∈ pairs.map (fun | .@@PAIR_CTOR@@ k v => (k, v)), " ++
  "keys pair.1 ∧ valid pair.2 := by\n" ++
  "      intro pair member\n" ++
  "      obtain ⟨pair, belongs, rfl⟩ := List.mem_map.mp member\n" ++
  "      cases pair with\n" ++
  "      | @@PAIR_CTOR@@ k v => exact hf _ belongs\n" ++
  "    exact ProducerMap.update (fun pair => keys pair.1 ∧ valid pair.2)\n" ++
  "      _ key value all ⟨hk, hv⟩ _ belongs\n" ++
  "\n" ++
  "#audit_axioms addMapValid\n" ++
  "\n" ++
  "private theorem addVarValid (keys : @@KEY_TYPE@@ → Prop) " ++
  "(valid : @@VALUE_TYPE@@ → Prop) (other) (scope : @@SCOPE_TYPE@@)\n" ++
  "    (ctx : @@CONTEXT_TYPE@@) (key : @@KEY_TYPE@@) (value : @@VALUE_TYPE@@)\n" ++
  "    (accepted : contextValid keys valid other ctx) " ++
  "(keyValid : keys key) (valueValid : valid value) :\n" ++
  "    Produces (contextValid keys valid other)\n" ++
  "      (ExceptT.mk (@@CALLABLE@@ scope ctx key value)) := by\n" ++
  "  unfold @@CALLABLE@@\n" ++
  "  apply Produces.orElse\n" ++
  "  · apply Produces.bindAny; intro _\n" ++
  "    apply Produces.bindAny; intro _\n" ++
  "    apply Produces.bindAny; intro _\n" ++
  "    apply Produces.bindAny; intro _\n" ++
  "    refine Produces.bind (k := fun frame => pure { ctx with @@GLOBAL_PATH@@ := frame })\n" ++
  "      (addMapValid keys valid _ key value accepted.2.1 keyValid valueValid) ?_\n" ++
  "    intro frame acceptedFrame\n" ++
  "    apply Produces.pure\n" ++
  "    exact ⟨accepted.1, acceptedFrame, accepted.2.2⟩\n" ++
  "  · apply Produces.orElse\n" ++
  "    · apply Produces.bindAny; intro _\n" ++
  "      apply Produces.bindAny; intro _\n" ++
  "      apply Produces.bindAny; intro _\n" ++
  "      apply Produces.bindAny; intro _\n" ++
  "      refine Produces.bind (k := fun frame => pure { ctx with @@BLOCK_PATH@@ := frame })\n" ++
  "        (addMapValid keys valid _ key value accepted.2.2.1 keyValid valueValid) ?_\n" ++
  "      intro frame acceptedFrame\n" ++
  "      apply Produces.pure\n" ++
  "      exact ⟨accepted.1, accepted.2.1, acceptedFrame, accepted.2.2.2⟩\n" ++
  "    · apply Produces.bindAny; intro _\n" ++
  "      apply Produces.bindAny; intro _\n" ++
  "      cases frames : @@LOCAL_ACCESS@@ with\n" ++
  "      | nil => exact Produces.error _ _\n" ++
  "      | cons head tail =>\n" ++
  "        have acceptedFrames := accepted.2.2.2\n" ++
  "        rw [frames] at acceptedFrames\n" ++
  "        apply Produces.bindAny; intro _\n" ++
  "        apply Produces.bindAny; intro _\n" ++
  "        apply Produces.bindAny; intro _\n" ++
  "        refine Produces.bind " ++
  "(k := fun frame => pure { ctx with @@LOCAL_PATH@@ := frame :: tail })\n" ++
  "          (addMapValid keys valid head key value (acceptedFrames head (by simp))\n" ++
  "            keyValid valueValid) ?_\n" ++
  "        intro frame acceptedFrame\n" ++
  "        apply Produces.pure\n" ++
  "        refine ⟨accepted.1, accepted.2.1, accepted.2.2.1, ?_⟩\n" ++
  "        intro element member\n" ++
  "        rcases List.mem_cons.mp member with rfl | member\n" ++
  "        · exact acceptedFrame\n" ++
  "        · exact acceptedFrames element (List.mem_cons_of_mem _ member)\n" ++
  "\n" ++
  "#audit_axioms addVarValid\n"

private def named (env : Env) (name : String) : String := env.q (Names.typeName name)

private def fieldName (field : atom) : String := Names.fieldName field.it

private def access (base : String) (path : FieldPath) : String :=
  base ++ "." ++ fieldName path.outer ++ "." ++ fieldName path.inner

private def sourceNominal (env : Env) (name value : String) : Except String String :=
  Producer.admission env (Q.t (Q.varT name [])) value

private def conjunction (facts : List String) : String :=
  if facts.isEmpty then "True" else " ∧\n    ".intercalate facts

/-- Exact admission of every map projected at the three source-checked insertion paths. -/
def callInputTheoremType (env : Env) (d : Lang.Al.def) : Except String String := do
  let plan ← insertPlan env d
  let [global, block, localPath] := plan.paths | throw "context insertion path count differs"
  let mapType := Q.t (Q.varT plan.frame.map [plan.frame.key, plan.frame.payload])
  let prior ← sourceNominal env global.context.name "ctx"
  let first ← Producer.admission env mapType ("(" ++ access "ctx" global ++ ")")
  let second ← Producer.admission env mapType ("(" ++ access "ctx" block ++ ")")
  let frames ← Producer.admission env mapType "frame"
  pure (s!"∀ (ctx : {named env global.context.name}),\n{prior} →\n" ++
    first ++ " ∧\n" ++ second ++ " ∧\n" ++
    s!"(∀ frame ∈ {access "ctx" localPath}, {frames})")

private def insertDeclarations (env : Env) (d : Lang.Al.def) (plan : InsertPlan) :
    Except String Std.Format := do
  let [global, block, localPath] := plan.paths | throw "context insertion needs three checked paths"
  let namespaceName := Names.typeName (plan.callable ++ "ContextProducer")
  let otherFields := global.layer.fields.filter fun field =>
    Names.fieldName field.1.it != fieldName global.inner
  let otherTypes := otherFields.map fun (_, type) => (typTerm env [] type.it).fmt.pretty
  let otherType := " → ".intercalate (otherTypes ++ ["Prop"])
  let otherBinders := otherTypes.zipIdx.map fun (type, index) => s!"(o{index} : {type})"
  let otherFacts ← otherFields.zipIdx.mapM fun ((_, type), index) =>
    Producer.admission env type s!"o{index}"
  let otherAccess := otherFields.map fun (field, _) =>
    "ctx." ++ fieldName global.outer ++ "." ++ fieldName field
  let roles := [("KEY_TYPE", (typTerm env [] plan.frame.key.it).fmt.pretty),
    ("VALUE_TYPE", (typTerm env [] plan.frame.payload.it).fmt.pretty),
    ("FRAME_TYPE", named env plan.frame.name), ("CONTEXT_TYPE", named env global.context.name),
    ("SCOPE_TYPE", named env plan.scope), ("OTHER_TYPE", otherType),
    ("OTHER_ACCESS", " ".intercalate otherAccess),
    ("GLOBAL_ACCESS", access "ctx" global), ("BLOCK_ACCESS", access "ctx" block),
    ("LOCAL_ACCESS", access "ctx" localPath),
    ("GLOBAL_PATH", fieldName global.outer ++ "." ++ fieldName global.inner),
    ("BLOCK_PATH", fieldName block.outer ++ "." ++ fieldName block.inner),
    ("LOCAL_PATH", fieldName localPath.outer ++ "." ++ fieldName localPath.inner),
    ("SET", named env plan.frame.set), ("PAIR", named env plan.frame.pair),
    ("SET_CTOR", plan.frame.setConstructor), ("PAIR_CTOR", plan.frame.pairConstructor),
    ("INSERTION", env.q (Names.funcName plan.insertion)),
    ("CALLABLE", env.q (Names.funcName plan.callable))]
  let keyDomain ← Producer.admission env plan.frame.key "x"
  let valueDomain ← Producer.admission env plan.frame.payload "x"
  let domain := "/-- Actual source admission of map keys. -/\n" ++
    s!"private def keyDomain (x : {(typTerm env [] plan.frame.key.it).fmt.pretty}) :=\n" ++
    "  " ++ keyDomain ++ "\n\n/-- Actual source admission of stored values. -/\n" ++
    s!"private def valueDomain (x : {(typTerm env [] plan.frame.payload.it).fmt.pretty}) :=\n" ++
    "  " ++ valueDomain ++ "\n\n/-- Source admission of all untouched global fields. -/\n" ++
    "private def otherDomain " ++ " ".intercalate otherBinders ++ " : Prop :=\n  " ++
    conjunction otherFacts
  let record := named env global.context.name
  let layers := [global.layer.name, block.layer.name, localPath.layer.name]
  let sourceIff := "/-- Exact source record and alias domains agree with the context model. -/\n" ++
    s!"private theorem sourceIff (ctx : {record}) :\n" ++
    s!"    {record}.source ({record}.toValue ctx) ↔\n" ++
    "      contextValid keyDomain valueDomain otherDomain ctx := by\n" ++
    String.join (layers.zipIdx.map fun (layer, index) =>
      s!"  have layer{index}Iff := {named env layer}.encodingSourceIff\n" ++
      s!"  simp only [{named env layer}.source] at layer{index}Iff\n") ++
    s!"  have frameIff := {named env plan.frame.name}.encodingSourceIff\n" ++
    s!"  simp only [{named env plan.frame.name}.source] at frameIff\n" ++
    "  delta keyDomain valueDomain\n" ++
    "  dsimp only [contextValid, frameValid, otherDomain]\n" ++
    s!"  simp only [{record}.encodingSourceIff, layer0Iff, layer1Iff, layer2Iff,\n" ++
    s!"    frameIff, {named env plan.frame.map}.encodingSourceIff,\n" ++
    "    Representation.Source.encodedListIff, true_and, and_assoc, and_left_comm, and_comm]\n" ++
    "\n#audit_axioms sourceIff"
  let mapType := Q.t (Q.varT plan.frame.map [plan.frame.key, plan.frame.payload])
  let mapDomain ← Producer.admission env mapType "x"
  let frameIff :=
    "/-- Bare generic map admission uses its actual declared key and value types. -/\n" ++
    s!"private theorem frameSourceIff (x : {named env plan.frame.name}) :\n" ++
    "    " ++ mapDomain ++ " ↔ frameValid keyDomain valueDomain x := by\n" ++
    "  dsimp only [frameValid, keyDomain, valueDomain]\n" ++
    s!"  exact @{named env plan.frame.map}.encodingSourceIff\n" ++
    s!"    ({(typTerm env [] plan.frame.key.it).fmt.pretty})\n" ++
    s!"    ({(typTerm env [] plan.frame.payload.it).fmt.pretty})\n" ++
    "    ⟨" ++ (← Producer.encoder env plan.frame.key) ++ "⟩\n" ++
    "    ⟨" ++ (← Producer.encoder env plan.frame.payload) ++ "⟩\n" ++
    "    (" ++ (Reify.typ plan.frame.key).fmt.pretty ++ ")\n" ++
    "    (" ++ (Reify.typ plan.frame.payload).fmt.pretty ++ ") x\n\n" ++
    "#audit_axioms frameSourceIff"
  let projectionType ← callInputTheoremType env d
  let projection :=
    "/-- All reachable projected map arguments belong to their source domains. -/\n" ++
    s!"theorem {Names.funcName plan.callable}.callInputsSource : {projectionType} := by\n" ++
    "  intro ctx accepted\n" ++
    s!"  change {record}.source ({record}.toValue ctx) at accepted\n" ++
    s!"  have valid := ({namespaceName}.sourceIff ctx).mp accepted\n" ++
    s!"  refine ⟨({namespaceName}.frameSourceIff _).mpr valid.2.1,\n" ++
    s!"    ({namespaceName}.frameSourceIff _).mpr valid.2.2.1, ?_⟩\n" ++
    "  intro frame member\n" ++
    s!"  exact ({namespaceName}.frameSourceIff _).mpr (valid.2.2.2 frame member)\n\n" ++
    s!"#audit_axioms {Names.funcName plan.callable}.callInputsSource"
  let statement ← Producer.theoremType env d
  let output := s!"namespace {namespaceName}\n\n" ++ (← template insertionTemplate roles) ++
    "\n\n" ++ domain ++ "\n\n" ++ sourceIff ++ "\n\n" ++ frameIff ++
    s!"\n\nend {namespaceName}\n\n" ++
    "/-- Successful context insertion preserves the complete independent source grammar. -/\n" ++
    s!"theorem {Names.funcName plan.callable}.producesSource : {statement} := by\n" ++
    "  intro scope ctx key value _ accepted keyValid valueValid result run\n" ++
    s!"  change {record}.source ({record}.toValue ctx) at accepted\n" ++
    s!"  have preserved := {namespaceName}.addVarValid {namespaceName}.keyDomain\n" ++
    s!"    {namespaceName}.valueDomain {namespaceName}.otherDomain scope ctx key value\n" ++
    s!"    (({namespaceName}.sourceIff ctx).mp accepted) keyValid valueValid\n" ++
    s!"  change {record}.source ({record}.toValue result)\n" ++
    s!"  exact ({namespaceName}.sourceIff result).mpr (preserved result run)\n\n" ++
    s!"#audit_axioms {Names.funcName plan.callable}.producesSource\n\n" ++ projection
  pure (Std.Format.text (boundedLines output))

private def exitDeclarations (env : Env) (d : Lang.Al.def) (plan : ExitPlan) :
    Except String Std.Format := do
  let path := plan.path
  let namespaceName := Names.typeName (plan.callable ++ "ContextProducer")
  let record := named env path.context.name
  let layer := named env path.layer.name
  let element := (typTerm env [] plan.element.it).fmt.pretty
  let others := path.context.fields.filter fun field =>
    Names.fieldName field.1.it != fieldName path.outer
  let otherType := " → ".intercalate ((others.map fun (_, type) =>
    (typTerm env [] type.it).fmt.pretty) ++ ["Prop"])
  let otherBinders := others.zipIdx.map fun ((_, type), index) =>
    s!"(o{index} : {(typTerm env [] type.it).fmt.pretty})"
  let otherFacts ← others.zipIdx.mapM fun ((_, type), index) =>
    Producer.admission env type s!"o{index}"
  let domain := "/-- Source admission of the selected list elements. -/\n" ++
    s!"private def elementDomain (x : {element}) :=\n  " ++
    (← Producer.admission env plan.element "x") ++
    "\n\n/-- Complete source domains of untouched context layers. -/\n" ++
    "private def otherDomain " ++ " ".intercalate otherBinders ++ " : Prop :=\n  " ++
    conjunction otherFacts
  let otherAccess := others.map fun (field, _) => "ctx." ++ fieldName field
  let model :=
    "/-- Context admission requires all untouched layers and selected list elements. -/\n" ++
    s!"private def contextValid (valid : {element} → Prop) (other : {otherType})\n" ++
    s!"    (ctx : {record}) : Prop :=\n" ++
    "  other " ++ " ".intercalate otherAccess ++ " ∧\n" ++
    s!"    ∀ frame ∈ {access "ctx" path}, valid frame"
  let pattern := path.context.fields.zipIdx.map fun ((field, _), index) =>
    if Names.fieldName field.it == fieldName path.outer then "⟨frames⟩" else s!"layer{index}"
  let output := path.context.fields.zipIdx.map fun ((field, _), index) =>
    if Names.fieldName field.it == fieldName path.outer then "⟨tail⟩" else s!"layer{index}"
  let exit := "/-- The checked list-tail operation preserves every retained element. -/\n" ++
    s!"private theorem exitValid (valid : {element} → Prop) (other) (ctx : {record})\n" ++
    "    (accepted : contextValid valid other ctx) :\n" ++
    "    Produces (contextValid valid other) " ++
    s!"(ExceptT.mk ({env.q (Names.funcName plan.callable)} ctx)) := by\n" ++
    "  rcases ctx with ⟨" ++ ", ".intercalate pattern ++ "⟩\n" ++
    "  cases frames with\n  | nil =>\n    intro result run\n    cases run\n" ++
    "  | cons head tail =>\n    intro result run\n" ++
    "    have same : result = ⟨" ++ ", ".intercalate output ++ "⟩ :=\n" ++
    "      (Except.ok.inj (Option.some.inj run)).symm\n    subst result\n" ++
    "    exact ⟨accepted.1, fun frame member =>\n" ++
    "      accepted.2 frame (List.mem_cons_of_mem _ member)⟩\n\n#audit_axioms exitValid"
  let sourceIff := "/-- Actual source record domains agree with the selected list model. -/\n" ++
    s!"private theorem sourceIff (ctx : {record}) :\n" ++
    s!"    {record}.source ({record}.toValue ctx) ↔\n" ++
    "      contextValid elementDomain otherDomain ctx := by\n" ++
    s!"  have localIff := {layer}.encodingSourceIff\n" ++
    s!"  simp only [{layer}.source] at localIff\n" ++
    "  delta elementDomain\n  dsimp only [contextValid, otherDomain]\n" ++
    s!"  simp only [{record}.encodingSourceIff, localIff,\n" ++
    "    Representation.Source.encodedListIff, true_and, and_assoc, and_left_comm, and_comm]\n" ++
    "\n#audit_axioms sourceIff"
  let statement ← Producer.theoremType env d
  let proof := s!"namespace {namespaceName}\n\n" ++ "\n\n".intercalate
    [model, exit, domain, sourceIff] ++ s!"\n\nend {namespaceName}\n\n" ++
    "/-- Successful list-tail exit preserves the complete independent source grammar. -/\n" ++
    s!"theorem {Names.funcName plan.callable}.producesSource : {statement} := by\n" ++
    "  intro ctx accepted result run\n" ++
    s!"  change {record}.source ({record}.toValue ctx) at accepted\n" ++
    s!"  have preserved := {namespaceName}.exitValid {namespaceName}.elementDomain\n" ++
    s!"    {namespaceName}.otherDomain ctx (({namespaceName}.sourceIff ctx).mp accepted)\n" ++
    s!"  change {record}.source ({record}.toValue result)\n" ++
    s!"  exact ({namespaceName}.sourceIff result).mpr (preserved result run)\n\n" ++
    s!"#audit_axioms {Names.funcName plan.callable}.producesSource"
  pure (Std.Format.text (boundedLines proof))

/-- Render a source-checked insertion or list-tail exit without a callable-name whitelist. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String Std.Format := do
  match insertPlan env d with
  | .ok plan => insertDeclarations env d plan
  | .error _ => exitDeclarations env d (← exitPlan env d)

/-- Exact representation sidecars used by the checked source context model. -/
def dependencies (env : Env) (d : Lang.Al.def) : Except String (List String) := do
  match insertPlan env d with
  | .ok plan =>
    let some first := plan.paths.head? | throw "context producer path is absent"
    pure (([first.context.name, plan.frame.name, plan.frame.map] ++
      plan.paths.map (·.layer.name)).eraseDups)
  | .error _ =>
    let plan ← exitPlan env d
    pure [plan.path.context.name, plan.path.layer.name]

end P4SpecTec.Codegen.ProducerContextProof
