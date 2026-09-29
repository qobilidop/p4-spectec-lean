import NanoP4Target.Externs
import NanoP4Spec.Refinement.Externs
import NanoP4Spec.Refinement.find_var_e
import NanoP4Spec.Refinement.update_var_e
import NanoP4Spec.Refinement.write_value_from_bits
import P4SpecTec.BackendSim.NanoSwitch.PipeContract
import P4SpecTec.Tactic.Audit

/-!
# NanoP4Target.Contract

The concrete NanoSwitch target discharges the abstract extern contract that every
extern-dependent Nano certificate assumes (`NanoP4Spec.externsContract`, design section 9.3).
The reference side is the dynamic port registered in the interpreter configuration
(`Pipe.externInterface`), calling back through the interpreter's own function evaluator at
every trampoline fuel; the generated side is the typed instance `NanoP4Target.externs`.
Both directions hold for every global context satisfying the specification and every
related input, including non-PACKET receivers, undecodable payloads, other methods, short
packets, parse failures and failing callees; not an upstream mirror.
-/

namespace NanoP4Target

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Lang.Il
open P4SpecTec.BackendSim P4SpecTec.BackendSim.NanoSwitch

/-- A reference configuration of the concrete target: NanoSwitch externs registered and
dynamic guards off. Print hints and tracing are unconstrained. -/
structure Reference (cfg : Interp_al.Interp.Config) : Prop where
  /-- The registered extern implementation is the NanoSwitch port. -/
  extern : cfg.extern = Pipe.externInterface
  /-- Dynamic type guards are off, as in the certified profile. -/
  guard : cfg.guard = false

/-- The trampoline an extern call receives: the interpreter's function evaluator at `fuel`,
registered through upstream's failure collapse. -/
abbrev trampoline (cfg : Interp_al.Interp.Config) (g : Interp_al.Ctx.global) (fuel : Nat) :
    Pipe.Call Eval :=
  Make.call_func (Interp_al.Interp.do_eval_func fuel cfg g)

/-- The reference configuration is inhabited: the NanoSwitch externs with guards off and the
pinned empty print hints, the configuration the session replay runs. -/
theorem referenceWitness :
    Reference { guard := false, extern := Pipe.externInterface } ∧
      ({ guard := false, extern := Pipe.externInterface } :
        Interp_al.Interp.Config).printHints = [] :=
  ⟨⟨rfl, rfl⟩, rfl⟩

#audit_axioms referenceWitness

/-- Extract's intermediate result: the same packet and related contexts. -/
def ExtractRel (a : Core.Object.PacketIn.t × value)
    (b : Core.Object.PacketIn.t × NanoP4Spec.evalContext) : Prop :=
  a.1 = b.1 ∧ Rel a.2 b.2

/-- The reference's local scope argument is the generated `LOCAL`. -/
theorem localScopeRel :
    Rel (Runtime.Value.Make.case (Pipe.varT "scope")
      (.Atom (Util.Source.mkPhrase (.Keyword "LOCAL")))) NanoP4Spec.scope.LOCAL := rfl

/-- The reference's header name argument is the generated `hdr`. -/
theorem hdrRel : Rel (Runtime.Value.Make.text (ByteText.ofString "hdr")) hdr := rfl

/-- The reference's header bits are the generated bit list. -/
theorem bitsRel (bits : Core.Object.bits) :
    Rel (Runtime.Value.Make.list (.IterT (Util.Source.mkPhrase (Pipe.varT "bit")) .List)
      (bits.toList.map Runtime.Value.Make.bool)) (bits.toList : NanoP4Spec.bits) := by
  simp only [Rel, canon]
  congr 2

section Callees

variable {cfg : Interp_al.Interp.Config} {g : Interp_al.Ctx.global}

/-- Forward correspondence of the trampoline's `find_var_e` call. -/
theorem findVarRefines (hcfg : Reference cfg) (hspec : HoldsSpec NanoP4Spec.spec g)
    (fuel : Nat) {vctx : value} {ctx : NanoP4Spec.evalContext} (hctx : Rel vctx ctx) :
    Refines Rel
      (trampoline cfg g fuel "find_var_e" []
        [Runtime.Value.Make.case (Pipe.varT "scope")
          (.Atom (Util.Source.mkPhrase (.Keyword "LOCAL"))), vctx,
         Runtime.Value.Make.text (ByteText.ofString "hdr")])
      (callee (NanoP4Spec.«$find_var_e» .LOCAL ctx hdr)) :=
  refines_catchUnmatch (NanoP4Spec.«$find_var_e».refines fuel cfg (Interp_al.Ctx.empty g) false
    hcfg.guard rfl hspec _ _ _ _ _ _ localScopeRel hctx hdrRel)

/-- Reverse correspondence of the trampoline's `find_var_e` call. -/
theorem findVarRealizes (hcfg : Reference cfg) (hspec : HoldsSpec NanoP4Spec.spec g)
    {vctx : value} {ctx : NanoP4Spec.evalContext} (hctx : Rel vctx ctx) :
    Realizes Rel
      (fun fuel => trampoline cfg g fuel "find_var_e" []
        [Runtime.Value.Make.case (Pipe.varT "scope")
          (.Atom (Util.Source.mkPhrase (.Keyword "LOCAL"))), vctx,
         Runtime.Value.Make.text (ByteText.ofString "hdr")])
      (callee (NanoP4Spec.«$find_var_e» .LOCAL ctx hdr)) :=
  realizes_catchUnmatch (NanoP4Spec.«$find_var_e».realizes cfg (Interp_al.Ctx.empty g) false
    hcfg.guard rfl hspec _ _ _ _ _ _ localScopeRel hctx hdrRel)

/-- Forward correspondence of the trampoline's `write_value_from_bits` call. -/
theorem writeBitsRefines (hcfg : Reference cfg) (hspec : HoldsSpec NanoP4Spec.spec g)
    (fuel : Nat) {vhdr : value} {h : NanoP4Spec.value} (hhdr : Rel vhdr h)
    (bits : Core.Object.bits) :
    Refines Rel
      (trampoline cfg g fuel "write_value_from_bits" []
        [vhdr, Runtime.Value.Make.list (.IterT (Util.Source.mkPhrase (Pipe.varT "bit")) .List)
          (bits.toList.map Runtime.Value.Make.bool)])
      (callee (NanoP4Spec.«$write_value_from_bits» h bits.toList)) :=
  refines_catchUnmatch (NanoP4Spec.«$write_value_from_bits».refines fuel cfg
    (Interp_al.Ctx.empty g) false hcfg.guard rfl hspec _ _ _ _ hhdr (bitsRel bits))

/-- Reverse correspondence of the trampoline's `write_value_from_bits` call. -/
theorem writeBitsRealizes (hcfg : Reference cfg) (hspec : HoldsSpec NanoP4Spec.spec g)
    {vhdr : value} {h : NanoP4Spec.value} (hhdr : Rel vhdr h) (bits : Core.Object.bits) :
    Realizes Rel
      (fun fuel => trampoline cfg g fuel "write_value_from_bits" []
        [vhdr, Runtime.Value.Make.list (.IterT (Util.Source.mkPhrase (Pipe.varT "bit")) .List)
          (bits.toList.map Runtime.Value.Make.bool)])
      (callee (NanoP4Spec.«$write_value_from_bits» h bits.toList)) :=
  realizes_catchUnmatch (NanoP4Spec.«$write_value_from_bits».realizes cfg
    (Interp_al.Ctx.empty g) false hcfg.guard rfl hspec _ _ _ _ hhdr (bitsRel bits))

/-- Forward correspondence of the trampoline's `update_var_e` call. -/
theorem updateVarRefines (hcfg : Reference cfg) (hspec : HoldsSpec NanoP4Spec.spec g)
    (hK : g.tdtbl.get? "K" = none) (hV : g.tdtbl.get? "V" = none) (fuel : Nat)
    {vctx vhdr : value} {ctx : NanoP4Spec.evalContext} {h : NanoP4Spec.value}
    (hctx : Rel vctx ctx) (hhdr : Rel vhdr h) :
    Refines Rel
      (trampoline cfg g fuel "update_var_e" []
        [Runtime.Value.Make.case (Pipe.varT "scope")
          (.Atom (Util.Source.mkPhrase (.Keyword "LOCAL"))), vctx,
         Runtime.Value.Make.text (ByteText.ofString "hdr"), vhdr])
      (callee (NanoP4Spec.«$update_var_e» .LOCAL ctx hdr h)) :=
  refines_catchUnmatch (NanoP4Spec.«$update_var_e».refines fuel cfg (Interp_al.Ctx.empty g)
    false hcfg.guard rfl hspec hK hV _ _ _ _ _ _ _ _ localScopeRel hctx hdrRel hhdr)

/-- Reverse correspondence of the trampoline's `update_var_e` call. -/
theorem updateVarRealizes (hcfg : Reference cfg) (hspec : HoldsSpec NanoP4Spec.spec g)
    (hK : g.tdtbl.get? "K" = none) (hV : g.tdtbl.get? "V" = none)
    {vctx vhdr : value} {ctx : NanoP4Spec.evalContext} {h : NanoP4Spec.value}
    (hctx : Rel vctx ctx) (hhdr : Rel vhdr h) :
    Realizes Rel
      (fun fuel => trampoline cfg g fuel "update_var_e" []
        [Runtime.Value.Make.case (Pipe.varT "scope")
          (.Atom (Util.Source.mkPhrase (.Keyword "LOCAL"))), vctx,
         Runtime.Value.Make.text (ByteText.ofString "hdr"), vhdr])
      (callee (NanoP4Spec.«$update_var_e» .LOCAL ctx hdr h)) :=
  realizes_catchUnmatch (NanoP4Spec.«$update_var_e».realizes cfg (Interp_al.Ctx.empty g)
    false hcfg.guard rfl hspec hK hV _ _ _ _ _ _ _ _ localScopeRel hctx hdrRel hhdr)

end Callees

section Extract

variable {cfg : Interp_al.Interp.Config} {g : Interp_al.Ctx.global}

/-- Forward correspondence of extract on a decoded packet, at every trampoline fuel. -/
theorem extractRefines (hcfg : Reference cfg) (hspec : HoldsSpec NanoP4Spec.spec g)
    (hK : g.tdtbl.get? "K" = none) (hV : g.tdtbl.get? "V" = none) (fuel : Nat)
    (pkt : Core.Object.PacketIn.t) {vctx : value} {ctx : NanoP4Spec.evalContext}
    (hctx : Rel vctx ctx) :
    Refines ExtractRel (Pipe.extract (trampoline cfg g fuel) pkt vctx) (extract ctx pkt) := by
  unfold Pipe.extract extract
  by_cases hshort : Core.Object.hostAdd pkt.idx 24 > pkt.len
  · simp only [hshort, ↓reduceIte]
    exact refines_pure ⟨rfl, hctx⟩
  · simp only [hshort, ↓reduceIte]
    cases hparse : Core.Object.PacketIn.parse pkt 24 with
    | error e =>
      simp only [Pipe.checked]
      exact refines_throw
    | ok r =>
      obtain ⟨pkt', bits⟩ := r
      simp only [Pipe.checked, pure_bind]
      refine refines_bind (findVarRefines hcfg hspec fuel hctx) fun a b hab => ?_
      refine refines_bind (writeBitsRefines hcfg hspec fuel hab bits) fun a' b' hab' => ?_
      refine refines_bind (updateVarRefines hcfg hspec hK hV fuel hctx hab') fun c d hcd => ?_
      exact refines_pure ⟨rfl, hcd⟩

/-- Reverse correspondence of extract on a decoded packet. -/
theorem extractRealizes (hcfg : Reference cfg) (hspec : HoldsSpec NanoP4Spec.spec g)
    (hK : g.tdtbl.get? "K" = none) (hV : g.tdtbl.get? "V" = none)
    (pkt : Core.Object.PacketIn.t) {vctx : value} {ctx : NanoP4Spec.evalContext}
    (hctx : Rel vctx ctx) :
    Realizes ExtractRel (fun fuel => Pipe.extract (trampoline cfg g fuel) pkt vctx)
      (extract ctx pkt) := by
  unfold Pipe.extract extract
  by_cases hshort : Core.Object.hostAdd pkt.idx 24 > pkt.len
  · simp only [hshort, ↓reduceIte]
    exact Realizes.pure ⟨rfl, hctx⟩
  · simp only [hshort, ↓reduceIte]
    cases hparse : Core.Object.PacketIn.parse pkt 24 with
    | error e =>
      simp only [Pipe.checked]
      exact Realizes.error _ _
    | ok r =>
      obtain ⟨pkt', bits⟩ := r
      simp only [Pipe.checked, pure_bind]
      refine Realizes.bind (findVarRealizes hcfg hspec hctx) fun a b hab => ?_
      refine Realizes.bind (writeBitsRealizes hcfg hspec hab bits) fun a' b' hab' => ?_
      refine Realizes.bind (updateVarRealizes hcfg hspec hK hV hctx hab') fun c d hcd => ?_
      exact Realizes.pure ⟨rfl, hcd⟩

end Extract

/-- The generated parameter list is read back exactly by the reference's text-list access. -/
theorem textsToValue (names : List NanoP4Spec.nameIR) :
    Pipe.texts (toValue names) = some names := by
  show (names.map toValue).mapM Runtime.Value.Get.text = some names
  induction names with
  | nil => rfl
  | cons n ns ih => simp only [List.map_cons, List.mapM_cons, ih]; rfl

/-- The reference's receiver packet state for a generated receiver. -/
theorem packetStateToValue (p : NanoP4Spec.value) :
    Pipe.packet_state (toValue p) =
      match p with | .PACKET _ state => some state.json | _ => none := by
  cases p <;> rfl

/-- The raw serialized receiver and the generated runtime extern carrier are related. -/
theorem receiverOuts (json : Lean.Json) {vctx : value} {ctx : NanoP4Spec.evalContext}
    (hctx : Rel vctx ctx) :
    Outs [Runtime.Value.Make.extern (Pipe.varT "objectState") json, vctx]
      [toValue (NanoP4Spec.value.runtimeExtern ⟨json⟩), toValue ctx] := by
  have hctx' : canon vctx = canon (toValue ctx) := hctx
  simp only [Outs, canons, hctx']
  rfl

#audit_axioms localScopeRel
#audit_axioms hdrRel
#audit_axioms bitsRel
#audit_axioms findVarRefines
#audit_axioms findVarRealizes
#audit_axioms writeBitsRefines
#audit_axioms writeBitsRealizes
#audit_axioms updateVarRefines
#audit_axioms updateVarRealizes
#audit_axioms extractRefines
#audit_axioms extractRealizes
#audit_axioms textsToValue
#audit_axioms packetStateToValue
#audit_axioms receiverOuts

/-- The concrete NanoSwitch target discharges the abstract extern contract assumed by every
extern-dependent Nano certificate, in both directions, for every global context satisfying
the specification, every trampoline fuel and every related input. -/
theorem externsContractHolds {cfg : Interp_al.Interp.Config} (hcfg : Reference cfg) :
    NanoP4Spec.externsContract cfg := by
  intro g hspec _hX hK hV v0 v1 v2 v3 p0 p1 p2 p3 h0 h1 h2 h3
  have hdispatch : ∀ call : Interp_al.Interp.FuncCall Eval,
      cfg.extern.eval_extern_rel call "ExternMethodCall_eval" [v0, v1, v2, v3] =
        Pipe.eval_extern_method_call (Make.call_func call) [v0, v1, v2, v3] := by
    intro call
    rw [hcfg.extern]
    rfl
  have h2' : canon v2 = canon (toValue p2) := h2
  have h3' : canon v3 = canon (toValue p3) := h3
  have hname : Runtime.Value.Get.text v2 = some p2 := by
    rw [← Pipe.text_canon, h2', Pipe.text_canon]
    rfl
  have hnames : Pipe.texts v3 = some p3 := by
    rw [← Pipe.texts_canon, h3', Pipe.texts_canon]
    exact textsToValue p3
  have hstate := Pipe.packet_state_congr h1
  rw [packetStateToValue] at hstate
  simp only [hdispatch]
  show (∀ fuel, Refines _ _ (externMethodCall p0 p1 p2 p3)) ∧
    Realizes _ _ (externMethodCall p0 p1 p2 p3)
  cases p1
  case PACKET t state =>
    obtain ⟨json, hjson, hcompress⟩ : ∃ json, Pipe.packet_state v1 = some json ∧
        json.compress = state.json.compress := by
      cases hv : Pipe.packet_state v1 with
      | none => rw [hv] at hstate; cases hstate
      | some json => rw [hv] at hstate; exact ⟨json, rfl, Option.some.inj hstate⟩
    have hdecode : Pipe.extern_of_payload json = Pipe.extern_of_payload state.json := by
      simp only [Pipe.extern_of_payload, hcompress]
    simp only [Pipe.eval_extern_method_call, externMethodCall, Pipe.required, hjson, hname,
      hnames, hdecode, pure_bind]
    cases hdec : Pipe.extern_of_payload state.json with
    | error e =>
      simp only [Pipe.checked]
      exact ⟨fun _ => refines_throw, Realizes.error _ _⟩
    | ok ext =>
      obtain ⟨pkt⟩ := ext
      simp only [Pipe.checked, pure_bind]
      by_cases hm : Pipe.is_extract_hdr p2 p3
      · simp only [hm]
        refine ⟨fun fuel => refines_bind (extractRefines hcfg hspec hK hV fuel pkt h0)
          fun a b hab => ?_, Realizes.bind (extractRealizes hcfg hspec hK hV pkt h0)
          fun a b hab => ?_⟩
        · obtain ⟨a1, a2⟩ := a
          obtain ⟨b1, b2⟩ := b
          obtain ⟨rfl, hrel⟩ := hab
          exact refines_pure (receiverOuts _ hrel)
        · obtain ⟨a1, a2⟩ := a
          obtain ⟨b1, b2⟩ := b
          obtain ⟨rfl, hrel⟩ := hab
          exact Realizes.pure (receiverOuts _ hrel)
      · simp only [hm]
        exact ⟨fun _ => refines_throw, Realizes.error _ _⟩
  all_goals
    have hnone : Pipe.packet_state v1 = none := by
      cases hv : Pipe.packet_state v1 with
      | none => rfl
      | some json => rw [hv] at hstate; cases hstate
    simp only [Pipe.eval_extern_method_call, externMethodCall, Pipe.required, hnone]
    exact ⟨fun _ => refines_throw, Realizes.error _ _⟩

/-- info: 'NanoP4Target.externsContractHolds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externsContractHolds

end NanoP4Target
