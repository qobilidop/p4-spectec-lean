import P4SpecTec.Refine.Representation.SourceTuple
import P4SpecTec.Refine.Quote

/-! Contextual tuple dictionaries preserve source arity even when the right carrier is Prod. -/

namespace P4SpecTecTest.Refine.SourceTuple

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Refine.Representation

private def nested : Lang.Il.value :=
  @Source.pairEncoder Nat (Bool × Bool) inferInstance ⟨Source.pairEncoder⟩ (7, true, false)

#guard match nested.it with
  | .TupleV [_, inner] => match inner.it with
    | .TupleV [_, _] => true
    | _ => false
  | _ => false

-- The ambient closed product encoder flattens the right Prod; the contextual one does not.
#guard match (toValue (7, true, false)).it with
  | .TupleV [_, _, _] => true
  | _ => false
#guard @Source.pairDecoder Nat (Bool × Bool) inferInstance ⟨Source.pairDecoder⟩ 0 nested ==
  some (7, true, false)
#guard @Source.pairDecoder Nat Bool inferInstance inferInstance 0 nested == none
#guard @Source.pairDecoder Nat Bool inferInstance inferInstance 0
  (Runtime.Value.Make.tuple .TextT [toValue (7 : Nat), toValue true, toValue false]) == none
#guard Source.unitDecoder 0 (toValue ()) == some ()
#guard Source.unitDecoder 0 (Runtime.Value.Make.tuple .TextT [toValue true]) == none

example {spec externalDomain} :
    letI : ToValue (Bool × Bool) := ⟨Source.pairEncoder⟩
    letI : OfValue (Bool × Bool) := ⟨Source.pairDecoder⟩
    @Codec (Nat × (Bool × Bool)) ⟨Source.pairEncoder⟩ ⟨Source.pairDecoder⟩
      (Source.Valid spec externalDomain (.TupleT
        [Q.t (.NumT .NatT), Q.t (.TupleT [Q.t .BoolT, Q.t .BoolT])]))
      (fun _ => True ∧ (True ∧ True)) := by
  letI : ToValue (Bool × Bool) := ⟨Source.pairEncoder⟩
  letI : OfValue (Bool × Bool) := ⟨Source.pairDecoder⟩
  exact Source.pairCodec (Q.t (.NumT .NatT)) (Q.t (.TupleT [Q.t .BoolT, Q.t .BoolT]))
    (fun _ : Nat => True) (fun _ : Bool × Bool => True ∧ True) Source.natCodec
    (Source.pairCodec (Q.t .BoolT) (Q.t .BoolT)
      (fun _ : Bool => True) (fun _ : Bool => True) Source.boolCodec Source.boolCodec)

end P4SpecTecTest.Refine.SourceTuple
