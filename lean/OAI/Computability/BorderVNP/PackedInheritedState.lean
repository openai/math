import OAI.Computability.BorderVNP.PackedBankShift
import OAI.Computability.BorderVNP.CellDirectoryBoxRebase
import OAI.Computability.BorderVNP.CellDirectoryObservationLedger

/-! # Persistent site-local sparse histories

A site keeps its one-copy tables and earlier row blocks once. Every new layer
contributes only its interval ties. Local addresses start at zero. Each round
reserves the previous incident word area directly after the previous private
area, so a retained row continues to use exactly the same site-local integers.
A final cell gives the whole site one offset and its one-copy list one box
prefix.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open CellSparse
open scoped Classical

/-- A site-local private area, current incident area and persistent public row blocks.
The newest block is consed onto a shared list; older blocks are stored only once. -/
structure Site where
  /-- Size of the private and previously staged portion. -/
  work : ℕ
  /-- Number of bits in the current canonical incidence words of this site. -/
  incoming : ℕ
  /-- Opaque one-copy local tables, independent of movement and subsequent histograms. -/
  boxes : List (List Factor)
  /-- Newest-first history of concrete, site-local sparse record blocks. -/
  layers : List (List Record)

/-- Physical rows in chronological order, as expected by the factor sweep. -/
def Site.rows (s : Site) : List Record := s.layers.reverse.flatten

/-- Whole size of the intrinsic site-local bank, before final placement in a cell. -/
def Site.size (s : Site) : ℕ := s.work + s.incoming

/-- The actual unmerged site directory. Count reports are aggregated at the final cell. -/
def Site.directory (s : Site) : Directory := ⟨s.boxes,s.rows,[]⟩

/-- A compressed equality interval between two adjacent generations of the site's inputs. -/
structure Slice where
  /-- Start within the previous generation's concatenated incidence words. -/
  oldStart : ℕ
  /-- Start within the next generation's concatenated incidence words. -/
  newStart : ℕ
  /-- Number of consecutive bits tied by this single public record. -/
  width : ℕ
  deriving DecidableEq

/-- One equality row on two actual ranges in the persistent site-local bank. -/
def Slice.record (s : Site) (p : Slice) : Record :=
  .equal 1 p.width ⟨s.work+p.oldStart,0,1⟩ ⟨s.size+p.newStart,0,1⟩

/-- A retained site acquires exactly its old incidence words as private staging, and
shares all prior table and row data. -/
def Site.retain (s : Site) (newInput : ℕ) (cuts : List Slice) : Site :=
  ⟨s.size,newInput,s.boxes,(cuts.map (Slice.record s)) :: s.layers⟩

/-- Every prior row is retained once, followed by exactly one command per incoming interval. -/
theorem Site.retain_rows (s : Site) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).rows = s.rows ++ cuts.map (Slice.record s) := by
  simp [Site.retain,Site.rows,List.flatten_append]

/-- New rows never create a one-copy factor visit. Earlier visits, including their
relative address, copy ordinal, sign and selected table position, retain their order. -/
theorem Site.retain_occurrences (s : Site) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).directory.occurrences = s.directory.occurrences := by
  have hn : (cuts.flatMap (fun _ => ([] : List Occurrence))) = [] := by induction cuts <;> simp_all
  simp only [Site.directory,Directory.occurrences,Site.retain_rows,List.flatMap_append,List.flatMap_map,
    Slice.record,hn,List.append_nil]
  rfl

/-- The result seen by a local signed/tally table before aggregation of cell-wide
count reports. Absence denotes rejection; every successful factor observation is
retained, even a zero-valued gadget position. -/
noncomputable def Site.observe (s : Site) (bank : ℕ → Bool) : Option (List (Bool × Option ℕ)) :=
  if ∀ r ∈ s.rows, r.Valid s.boxes bank then s.directory.observations bank else none

/-- The new layer restricts only its interval equalities. All other checks and
all actual one-copy observations belong to the retained program. -/
theorem Site.observe_retain (s : Site) (n : ℕ) (cuts : List Slice) (bank : ℕ → Bool) :
    (s.retain n cuts).observe bank =
      if ∀ p ∈ cuts, (p.record s).Valid s.boxes bank then s.observe bank else none := by
  have obs : (s.retain n cuts).directory.observations bank = s.directory.observations bank := by
    unfold Directory.observations
    rw [s.retain_occurrences]
  simp only [Site.observe,Site.retain_rows,List.forall_mem_append,List.forall_mem_map,obs]
  change (if (∀ r ∈ s.rows, r.Valid s.boxes bank) ∧ (∀ p ∈ cuts, (p.record s).Valid s.boxes bank) then
      s.directory.observations bank else none) = _
  split_ifs <;> simp_all

/-- Row count grows additively along a retained history. -/
theorem Site.retain_count (s : Site) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).rows.length = s.rows.length + cuts.length := by
  rw [s.retain_rows,List.length_append,List.length_map]

/-- Final absolute records use the owning cell's bit prefix and merged one-copy box ordinal. -/
def Site.placedRows (s : Site) (offset boxOffset : ℕ) : List Record :=
  s.rows.map (fun r => (r.shift offset).rebaseBox boxOffset)

/-- A retained layer compiles by one reference to its predecessor's row block plus
the current translated slice commands. No table literal is duplicated. -/
theorem Site.placedRows_retain (s : Site) (n : ℕ) (cuts : List Slice) (offset boxOffset : ℕ) :
    (s.retain n cuts).placedRows offset boxOffset = s.placedRows offset boxOffset ++
      cuts.map (fun p => (p.record s).shift offset) := by
  simp only [Site.placedRows,Site.retain_rows,List.map_append,List.map_map]
  rfl

end Packing.Inherited

end BorderVNP
end Computability
end OAI
