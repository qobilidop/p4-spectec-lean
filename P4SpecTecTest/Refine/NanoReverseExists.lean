import P4SpecTecTest.Refine.NanoReverseExistsClauses
import P4SpecTec.Refine.Realize

/-!
Reverse execution of the actual recursive Nano `exists_` helper, using the
`partial_fixpoint` partial-correctness principle and its actual quoted AL clauses.
The proof covers every Boolean list and all raw inputs related to it, including
arbitrary notes. The first clause's mismatch is preserved before the recursive
clause consumes the tail eagerly. Generated hard errors are ruled out by the
induction, rather than omitted from the outcome quantifier. This is a handwritten
feasibility certificate, not generated coverage or an initialization theorem.
-/

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Interp_al
open Lean Elab Tactic Meta
open P4SpecTec.Lang.Il P4SpecTec.Domain
namespace P4SpecTecTest.NanoReverseExists

set_option maxRecDepth 8192

theorem consEventually (cfg : Interp.Config) (ctx : Ctx.t) (internal : Bool)
    (hg : cfg.guard = false) (hf : ctx.local.fenv = [])
    (hu : Holds ctx.global NanoP4Spec.«$exists_».al)
    (b c : Bool) (tail : List Lang.Il.value)
    (bn ln : Lang.Il.vnote) (ba la : Util.Source.region)
    (hrec : EventuallyRuns
      (fun fuel => Interp.invoke_func fuel cfg true
        (matchedCtx ctx ⟨.ListV (⟨.BoolV b,bn,ba⟩::tail),ln,la⟩
          ⟨.BoolV b,bn,ba⟩ tail ln.typ)
        (Q.i "exists_") [] [Runtime.Value.Make.list ln.typ tail])
      (.ok (Runtime.Value.Make.bool c))) :
    EventuallyRuns
      (fun fuel => Interp.invoke_func fuel cfg internal ctx (Q.i "exists_") []
        [⟨.ListV (⟨.BoolV b,bn,ba⟩::tail),ln,la⟩])
      (.ok (Runtime.Value.Make.bool (b || c))) := by
  obtain ⟨bound, hbound⟩ := hrec
  refine ⟨bound + 33, fun fuel hfuel => ?_⟩
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  have hcall := hbound (bound + extra + 26) (by omega)
  have hfuelEq : bound + 33 + extra = (bound + extra + 30) + 3 := by omega
  rw [hfuelEq]
  change Interp.invoke_func ((bound + extra + 30) + 3) cfg internal ctx
    (Q.i "exists_") [] [⟨.ListV (⟨.BoolV b,bn,ba⟩::tail),ln,la⟩] = _
  rw [invokeEq (bound + extra + 30) cfg ctx internal hg hf hu]
  have hfirst := firstCons (bound + extra + 15) cfg ctx ⟨.BoolV b,bn,ba⟩ tail ln la
  simp only [Nat.add_assoc] at hfirst ⊢
  have retry (m : Eval Lang.Il.value) : Eval.orElse (some (.error .unmatch)) m = m := rfl
  rw [hfirst, retry]
  have hpure (v : Lang.Il.value) : (pure v : Eval Lang.Il.value) = some (.ok v) := rfl
  simpa only [Nat.add_assoc, hpure] using
    recursiveClause (bound + extra) cfg ctx b tail bn ln ba la c hcall

/-- info: 'P4SpecTecTest.NanoReverseExists.consEventually' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms consEventually

private def Motive (bs : List Bool) (q : Except Fail Bool) : Prop :=
  ∀ (cfg : Interp.Config) (ctx : Ctx.t) (internal : Bool),
    cfg.guard = false → ctx.local.fenv = [] → HoldsSpec NanoP4Spec.spec ctx.global →
    ∀ raw : Lang.Il.value, Rel raw bs →
      ∃ b, q = .ok b ∧ EventuallyRuns
        (fun fuel => Interp.invoke_func fuel cfg internal ctx (Q.i "exists_") [] [raw])
        (.ok (Runtime.Value.Make.bool b))

set_option maxHeartbeats 200000 in
/-- Induction on the generated fixed point constructs an eventual reference
witness and excludes impossible generated failures without restricting inputs. -/
theorem realizesGenerated (bs : List Bool) (q : Except Fail Bool)
    (hq : NanoP4Spec.«$exists_» bs = some q) : Motive bs q := by
  apply NanoP4Spec.«$exists_».partial_correctness (motive := Motive) ?_ bs q hq
  intro rec ih bs q hq cfg ctx internal hg hf hs raw hr
  have hu := hs NanoP4Spec.«$exists_».al member
  obtain ⟨xs, hx, hc⟩ := rawOfRel hr
  cases raw with
  | mk rawIt ln la =>
    dsimp only at hx
    subst rawIt
    cases bs with
    | nil =>
      have hempty : xs = [] := canons_eq_nil hc
      subst xs
      have he : q = .ok false := by
        exact (Option.some.inj hq).symm
      refine ⟨false, he, 18, fun fuel hfuel => ?_⟩
      obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hfuel
      rw [Nat.add_comm 18 extra]
      change Interp.invoke_func ((extra + 15) + 3) cfg internal ctx
        (Q.i "exists_") [] [⟨.ListV [], ln, la⟩] = _
      rw [invokeEq (extra + 15) cfg ctx internal hg hf hu, nilRaw]
      rfl
    | cons b bs =>
      change canons xs = canon (toValue b) :: canons (bs.map toValue) at hc
      obtain ⟨head, tail, hxs, hh, ht⟩ := canons_eq_cons hc
      subst xs
      have hb := boolOfRel hh
      cases head with
      | mk headIt bn ba =>
        dsimp only at hb
        subst headIt
        let tailRaw := Runtime.Value.Make.list ln.typ tail
        have htail : Rel tailRaw bs := by
          change canon (Runtime.Value.Make.list ln.typ tail) = canon (toValue bs)
          simp only [ToValue.toValue, NanoP4Spec.bits.toValue, Runtime.Value.Make.list,
            Runtime.Value.Make.mk, Refine.canon, canon', ht]
        let nextCtx := matchedCtx ctx ⟨.ListV (⟨.BoolV b,bn,ba⟩::tail),ln,la⟩
          ⟨.BoolV b,bn,ba⟩ tail ln.typ
        change (do
          let v ← ExceptT.mk (rec bs)
          pure (b || v) : Eval Bool).run = some q at hq
        cases hrec : rec bs with
        | none => simp [hrec] at hq
        | some r =>
          have hnext : HoldsSpec NanoP4Spec.spec nextCtx.global := by
            change HoldsSpec NanoP4Spec.spec ctx.global
            exact hs
          have hfnext : nextCtx.local.fenv = [] := rfl
          have ihHere := ih bs r hrec
          dsimp only [Motive] at ihHere
          obtain ⟨c, hc, bound, hbound⟩ :=
            ihHere cfg nextCtx true hg hfnext hnext tailRaw htail
          subst r
          have hq' : q = .ok (b || c) := by
            rw [hrec] at hq
            exact (Option.some.inj hq).symm
          exact ⟨b || c, hq', consEventually cfg ctx internal hg hf hu
            b c tail bn ln ba la ⟨bound, hbound⟩⟩

/-- info: 'P4SpecTecTest.NanoReverseExists.realizesGenerated' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms realizesGenerated

/-- Every terminating generated outcome on the complete Boolean-list domain
has a related reference outcome at every sufficiently large fuel. Raw source
notes are arbitrary. Initialization is expressed by the existing `HoldsSpec`
contract, and the execution profile has guards disabled and no local functions. -/
theorem realizes (cfg : Interp.Config) (ctx : Ctx.t) (internal : Bool)
    (hg : cfg.guard = false) (hf : ctx.local.fenv = [])
    (hs : HoldsSpec NanoP4Spec.spec ctx.global)
    (raw : Lang.Il.value) (bs : List Bool) (hr : Rel raw bs) :
    Realizes Rel
      (fun fuel => Interp.invoke_func fuel cfg internal ctx (Q.i "exists_") [] [raw])
      (ExceptT.mk (NanoP4Spec.«$exists_» bs)) := by
  intro q hq
  obtain ⟨b, rfl, hb⟩ := realizesGenerated bs q hq cfg ctx internal hg hf hs raw hr
  exact ⟨.ok (Runtime.Value.Make.bool b), hb, rfl⟩

/-- info: 'P4SpecTecTest.NanoReverseExists.realizes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms realizes

end P4SpecTecTest.NanoReverseExists
