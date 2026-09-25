import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import P4SpecTec.Util.Source

/-!
Not a mirror: this module is ours, placed beside the module whose values it
decodes.

Not a mirror: this module is our own, placed beside the module it decodes.

Decoders for the JSON that `ppx_deriving_yojson` prints, the format of
upstream's `-json` export: records are objects, variants are arrays headed
by the constructor name, tuples and lists are arrays, options are `null`
or the value itself, unit is `null`, and bigints are decimal strings.
-/

namespace P4SpecTec.Util.Yojson

open Lean (Json)
open P4SpecTec.Util.Source

/-- A decoder from JSON. -/
abbrev D (α : Type) := Json → Except String α

/-- Fail with a message that shows a prefix of the offending JSON. -/
def fail {α : Type} (what : String) (j : Json) : Except String α :=
  let s := j.compress
  .error s!"{what}: {s.take 200}"

/-- Decode a string. -/
def str : D String
  | .str s => pure s
  | j => fail "expected string" j

/-- Decode a boolean. -/
def bool : D Bool
  | .bool b => pure b
  | j => fail "expected bool" j

/-- Decode an OCaml `int`. -/
def int : D Int
  | .num n => if n.exponent == 0 then pure n.mantissa else fail "expected int" (.num n)
  | j => fail "expected int" j

/-- Decode a bigint printed as a decimal string (or a plain number). -/
def bigint : D Int
  | .str s =>
    match s.toInt? with
    | some i => pure i
    | none => fail "expected bigint string" (.str s)
  | j => int j

/-- Decode `unit` (`null`). -/
def unit : D Unit
  | .null => pure ()
  | j => fail "expected null" j

/-- Decode a list. -/
def list {α : Type} (d : D α) : D (List α)
  | .arr a => a.toList.mapM d
  | j => fail "expected array" j

/-- Decode an option: `null` or the value. -/
def opt {α : Type} (d : D α) : D (Option α)
  | .null => pure none
  | j => some <$> d j

/-- Decode a pair (an array of two). -/
def pair {α β : Type} (da : D α) (db : D β) : D (α × β)
  | .arr #[a, b] => do pure (← da a, ← db b)
  | j => fail "expected pair" j

/-- Decode a triple (an array of three). -/
def triple {α β γ : Type} (da : D α) (db : D β) (dc : D γ) : D (α × β × γ)
  | .arr #[a, b, c] => do pure (← da a, ← db b, ← dc c)
  | j => fail "expected triple" j

/-- Decode a quadruple (an array of four). -/
def quad {α β γ δ : Type} (da : D α) (db : D β) (dc : D γ) (dd : D δ) : D (α × β × γ × δ)
  | .arr #[a, b, c, d] => do pure (← da a, ← db b, ← dc c, ← dd d)
  | j => fail "expected quadruple" j

/-- Split a variant into its constructor name and arguments. -/
def variant : D (String × Array Json)
  | .arr a =>
    match a.toList with
    | .str c :: rest => pure (c, rest.toArray)
    | _ => fail "expected variant" (.arr a)
  | j => fail "expected variant" j

/-- A field of an object. -/
def field (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => pure v
  | .error _ => fail s!"expected object with field {name}" j

/-- Decode a position. -/
def pos : D pos := fun j => do
  pure { file := ← str (← field j "file"), line := ← int (← field j "line"),
         column := ← int (← field j "column") }

/-- Decode a region. -/
def region : D region := fun j => do
  pure { left := ← pos (← field j "left"), right := ← pos (← field j "right") }

/-- Decode an `info` record. -/
def info {α β γ : Type} (dit : D α) (dnote : D β) (dat : D γ) : D (info α β γ) := fun j => do
  pure { it := ← dit (← field j "it"), note := ← dnote (← field j "note"),
         «at» := ← dat (← field j "at") }

/-- Decode a phrase. -/
def phrase {α : Type} (d : D α) : D (phrase α) := info d unit region

/-- Decode a note phrase. -/
def note_phrase {α β : Type} (d : D α) (dn : D β) : D (note_phrase α β) := info d dn region

/-- The arguments of a variant, checked for arity. -/
def args (c : String) (n : Nat) (a : Array Json) : Except String (Array Json) :=
  if a.size == n then pure a else .error s!"constructor {c}: expected {n} arguments, got {a.size}"

end P4SpecTec.Util.Yojson
