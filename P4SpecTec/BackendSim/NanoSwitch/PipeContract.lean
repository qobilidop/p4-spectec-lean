import P4SpecTec.BackendSim.NanoSwitch.Pipe
import P4SpecTec.Refine.ValueShape
import P4SpecTec.Tactic.Audit

/-!
Reusable contracts for the bounded dynamic NanoSwitch target; not an upstream mirror.
These branch facts preserve callback and fresh-state behavior. They do not discharge
the generated Nano extern contract or establish whole-program target composition.
-/

namespace P4SpecTec.BackendSim.NanoSwitch.Pipe

open P4SpecTec.Prelude

/-- A raw extern receiver is rejected before any callback, preserving the fresh counter. -/
theorem rawReceiverHandlerError (call : Call StateEval)
    (ctx method names : Lang.Il.value) (note : Lang.Il.typ') (json : Lean.Json)
    (state : FreshState) :
    StateEval.run (eval_extern_method_call call
      [ctx, Runtime.Value.Make.extern note json, method, names]) state =
      some (.error .err, state) := by
  rfl

/-- info: 'P4SpecTec.BackendSim.NanoSwitch.Pipe.rawReceiverHandlerError'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms rawReceiverHandlerError

open P4SpecTec.Runtime P4SpecTec.Util.Source

/-- Short-packet extract returns the raw serialized receiver and original context without
calling the callback or changing the fresh counter. The guard uses signed host addition. -/
theorem shortPacketExtract (call : Call StateEval) (ctx typeId : Lang.Il.value)
    (json : Lean.Json) (pkt : Core.Object.PacketIn.t) (state : FreshState)
    (decoded : extern_of_payload json = .ok (.PacketIn pkt))
    (short : Core.Object.hostAdd pkt.idx 24 > pkt.len) :
    StateEval.run (eval_extern_method_call call
      [ctx, Value.Make.case (varT "value")
        (.Seq [.Atom (mkPhrase (.Keyword "PACKET")), .Arg typeId,
          .Arg (Value.Make.extern (varT "objectState") json)]),
       Value.Make.text (ByteText.ofString "extract"),
       Value.Make.list (.IterT (mkPhrase (varT "nameIR")) .List)
         [Value.Make.text (ByteText.ofString "hdr")]]) state =
      some (.ok [Value.Make.extern (varT "objectState")
        (extern_to_yojson (.PacketIn pkt)), ctx], state) := by
  simp +decide [eval_extern_method_call, extract, packet_state, texts, is_extract_hdr,
    Value.Make.case, Value.Make.extern, Value.Make.text,
    Value.Make.list, Value.Make.mk, Value.Get.extern, Value.Get.text, Value.Get.list,
    required, checked, decoded, short, StateEval.run, List.mapM]
  rfl

/-- info: 'P4SpecTec.BackendSim.NanoSwitch.Pipe.shortPacketExtract'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shortPacketExtract

/-! ## Canonical invariance

Reference and generated values are related by canonical equality: notes and regions are
erased, and extern payloads are compared by their compressed JSON text. The accessors extract
uses observe only that canonical form, so related receivers, method names and parameter lists
give identical target behavior. -/

section Canonical

open P4SpecTec.Lang.Il P4SpecTec.Refine P4SpecTec.Domain

/-- Text access observes only the canonical form. -/
theorem text_canon (v : value) : Value.Get.text (canon v) = Value.Get.text v := by
  rcases v with ⟨it, n, r⟩
  rcases it with _ | _ | _ | _ | _ | _ | (_ | _) | _ | _ | _ <;> rfl

#audit_axioms text_canon

/-- Text-list access observes only the canonical form. -/
theorem texts_canon (v : value) : texts (canon v) = texts v := by
  rcases v with ⟨it, n, r⟩
  rcases it with _ | _ | _ | _ | _ | _ | (_ | _) | vs | _ | _ <;> try rfl
  show (canons vs).mapM Value.Get.text = vs.mapM Value.Get.text
  induction vs with
  | nil => rfl
  | cons w ws ih => simp only [canons, List.mapM_cons, text_canon, ih]

#audit_axioms texts_canon

/-- Extern-payload access observes the compressed text of the payload. -/
theorem extern_canon (v : value) :
    Value.Get.extern (canon v) = (Value.Get.extern v).map fun j => .str j.compress := by
  rcases v with ⟨it, n, r⟩
  rcases it with _ | _ | _ | _ | _ | _ | (_ | _) | _ | _ | _ <;> rfl

#audit_axioms extern_canon

/-- The receiver shape from which extract reads a packet state. -/
theorem packet_state_eq_some {v : value} {j : Lean.Json} :
    packet_state v = some j ↔ ∃ (a : Lang.Il.atom) (x s : value),
      v.it = .CaseV (.Seq [.Atom a, .Arg x, .Arg s]) ∧ (a.it == .Keyword "PACKET") = true ∧
        Value.Get.extern s = some j := by
  constructor
  · intro h
    unfold packet_state at h
    split at h
    · rename_i a x s hv
      by_cases ha : a.it == .Keyword "PACKET"
      · simp only [ha] at h
        exact ⟨a, x, s, hv, ha, by simpa using h⟩
      · simp [ha] at h
    · cases h
  · rintro ⟨a, x, s, hv, ha, hs⟩
    simp [packet_state, hv, ha, hs]

#audit_axioms packet_state_eq_some

/-- The receiver's packet state is observed through its compressed text. -/
theorem packet_state_canon (v : value) :
    packet_state (canon v) = (packet_state v).map fun j => .str j.compress := by
  cases hv : packet_state v with
  | some j =>
    obtain ⟨a, x, s, hit, ha, hs⟩ := packet_state_eq_some.mp hv
    apply packet_state_eq_some.mpr
    refine ⟨Util.Source.mkPhrase a.it, canon x, canon s, ?_, ha, ?_⟩
    · simp [canon_it, hit, canon', canonMixfix, canonMixfixes]
    · simp [extern_canon, hs]
  | none =>
    cases hc : packet_state (canon v) with
    | none => rfl
    | some j =>
      obtain ⟨a, x, s, hit, ha, hs⟩ := packet_state_eq_some.mp hc
      rw [canon_it] at hit
      obtain ⟨m, hm, hcm⟩ := canon'_eq_case hit
      obtain ⟨ms, rfl, hms⟩ := canonMixfix_eq_seq hcm
      obtain ⟨m1, ms, rfl, h1, hms⟩ := canonMixfixes_eq_cons hms
      obtain ⟨m2, ms, rfl, h2, hms⟩ := canonMixfixes_eq_cons hms
      obtain ⟨m3, ms, rfl, h3, hms⟩ := canonMixfixes_eq_cons hms
      cases canonMixfixes_eq_nil hms
      obtain ⟨a', rfl, ha'⟩ := canonMixfix_eq_atom h1
      obtain ⟨x', rfl, -⟩ := canonMixfix_eq_arg h2
      obtain ⟨s', rfl, rfl⟩ := canonMixfix_eq_arg h3
      rw [extern_canon] at hs
      cases hs' : Value.Get.extern s' with
      | none => rw [hs'] at hs; cases hs
      | some j' =>
        have := packet_state_eq_some.mpr ⟨a', x', s', hm, by rw [ha']; exact ha, hs'⟩
        rw [hv] at this
        cases this

#audit_axioms packet_state_canon

/-- Canonically equal receivers have packet states with equal compressed text. -/
theorem packet_state_congr {v w : value} (h : canon v = canon w) :
    (packet_state v).map Lean.Json.compress = (packet_state w).map Lean.Json.compress := by
  have hv := packet_state_canon v
  have hw := packet_state_canon w
  rw [h, hw] at hv
  cases hpv : packet_state v <;> cases hpw : packet_state w <;> simp_all

#audit_axioms packet_state_congr

end Canonical

end P4SpecTec.BackendSim.NanoSwitch.Pipe
