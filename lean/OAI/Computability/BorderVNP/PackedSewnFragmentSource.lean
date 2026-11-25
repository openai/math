import OAI.Computability.BorderVNP.FiniteSewnFieldRuns
import OAI.Computability.BorderVNP.ParseBatchSortCompare

/-! # Public interval fragments in the exterior sewing frame

The four words store the site, old start, positive width, and optional source
start. Two flags mark a live fragment and an occupied new source. Ordered
fragments are coalesced whenever the two partial translations continue.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open ParseBatchSort

/-- The enable and source-presence flags, followed by the four physical words. -/
abbrev Column (w : ℕ) := Bool ⊕ (Fin 4 × Fin w)

/-- The sparse physical rectangle with one slot for each possible fragment. -/
abbrev Pin (n w : ℕ) := Fin n × Column w

/-- A genuine fragment carries its site owner and its partial interval map. -/
structure Parsed where
  /-- Public ordinal of the site owning the predecessor interval. -/
  site : ℕ
  /-- Predecessor range and its partial translation into the new incidence word. -/
  run : Interval

/-- The scalar represented by one physical field. -/
def word {w : ℕ} (x : Column w → Bool) (k : Fin 4) : ℕ := value (fun j => x (.inr (k,j)))

/-- Decode one slot, interpreting its source word only on a sourced row. -/
def parseRow {w : ℕ} (x : Column w → Bool) : Parsed :=
  ⟨word x 0,⟨word x 1,word x 2,if x (.inl true) then some (word x 3) else none⟩⟩

/-- Enable bit of one slot of the fixed physical rectangle. -/
def active {n w : ℕ} (x : Pin n w → Bool) (i : Fin n) := x (i,.inl false)

/-- The site, old interval and optional new source stored at one physical slot. -/
def parse {n w : ℕ} (x : Pin n w → Bool) (i : Fin n) := parseRow (fun j => x (i,j))

/-- The true input list in physical order. -/
def list {n w : ℕ} (x : Pin n w → Bool) : List Parsed :=
  (List.finRange n).filterMap fun i => if active x i then some (parse x i) else none

/-- Consecutive fragments of the same site continue either a clamp or a translation. -/
def Parsed.compatible (a b : Parsed) : Prop :=
  a.site = b.site ∧ a.run.oldStart+a.run.width = b.run.oldStart ∧ a.run.source.map (·+a.run.width) = b.run.source

instance (a b : Parsed) : Decidable (a.compatible b) := by unfold Parsed.compatible; infer_instance

/-- Merge two continuing partial translations into the left-hand descriptor. -/
def Parsed.join (a b : Parsed) : Parsed := ⟨a.site,⟨a.run.oldStart,a.run.width+b.run.width,a.run.source⟩⟩

/-- Prepend a physical fragment to an already coalesced chronological list. -/
def prepend (a : Parsed) : List Parsed → List Parsed
  | [] => [a]
  | b::bs => if a.compatible b then a.join b::bs else a::b::bs

/-- The chronological list of maximal partial translations. -/
def coalesce (xs : List Parsed) : List Parsed := xs.foldr prepend []

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
