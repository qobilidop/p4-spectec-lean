/-!
Positions, regions and phrases. Mirrors `p4spec/lib/util/source.ml`
(P4-SpecTec, pinned in `upstream/`): the same record names and field
order, so the JSON export decodes field by field.
-/

namespace P4SpecTec.Util.Source

/-- A source position. Mirrors `pos`. -/
structure pos where
  /-- The file name as passed to upstream, relative to the repository root. -/
  file : String
  /-- One-based line. -/
  line : Int
  /-- Zero-based column. -/
  column : Int
  deriving BEq, Repr, Inhabited

/-- A source region. Mirrors `region`. -/
structure region where
  /-- Where the region starts. -/
  left : pos
  /-- Where the region ends. -/
  right : pos
  deriving BEq, Repr, Inhabited

/-- Mirrors `no_pos`. -/
def no_pos : pos := { file := "", line := 0, column := 0 }

/-- Mirrors `no_region`. -/
def no_region : region := { left := no_pos, right := no_pos }

/-- Mirrors `string_of_region`, for messages. -/
def string_of_region (r : region) : String :=
  s!"{r.left.file}:{r.left.line}.{r.left.column + 1}"

/-- A phrase with a payload, a note and a location. Mirrors `('a, 'b, 'c) info`. -/
structure info (α β γ : Type) where
  /-- The payload. -/
  it : α
  /-- The note; `Unit` for a plain phrase, a type for expressions. -/
  note : β
  /-- The location. -/
  «at» : γ
  deriving BEq, Repr

/-- Mirrors `('a, 'b) note_phrase`. -/
abbrev note_phrase (α β : Type) := info α β region

/-- Mirrors `'a phrase`. -/
abbrev phrase (α : Type) := info α Unit region

instance {α β γ} [Inhabited α] [Inhabited β] [Inhabited γ] : Inhabited (info α β γ) :=
  ⟨{ it := default, note := default, «at» := default }⟩

/-- Mirrors `( $ )`: a phrase at a region. -/
@[reducible] def mkPhrase {α : Type} (it : α) (region : region := no_region) : phrase α :=
  { it, note := (), «at» := region }

end P4SpecTec.Util.Source
