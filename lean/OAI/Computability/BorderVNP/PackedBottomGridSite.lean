import OAI.Computability.BorderVNP.PackedInheritedState
import OAI.Computability.BorderVNP.PackedBottomGridBank
import OAI.Computability.BorderVNP.PackedBottomGridRepeat
import OAI.Computability.BorderVNP.PackedBottomBankWitness
import OAI.Computability.BorderVNP.PackedGridFineCapacity

/-! # The complete one-copy directory and public birth program of a bottom site

The original fine factors, relocation checks and both padding tests are private.
The site-local public layer consists of one repeat box and one interval tie per
incident public word. The weighted sidecar remains the filtered list of genuine
original factors even after all padding and relocation checks are inserted.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports Inherited
open scoped Classical

/-- Private one-copy report padding also fixes the unused lanes before the final
absolute use-link descriptors are added to the cell. -/
def reportZeros (orig used cap : ℕ) : List Factor :=
  (List.range (cap-used)).map (fun k => GridPadding.zeroFactor (orig+used+k))

/-- Before and after assembly with the final report links, the private padding gives
one possible bit at every unused relative report address. -/
theorem reportZeros_pass (orig used cap off copy : ℕ) (bank : ℕ → Bool) :
    ((reportZeros orig used cap).all (fun f => (f.observe bank off copy).isSome)) = true ↔
      ∀ k < cap-used, bank (off+(orig+used+k)) = false := by
  simp only [reportZeros,List.all_eq_true,List.forall_mem_map,List.mem_range,GridPadding.observe_zero]
  constructor
  · intro h k hk
    cases he : bank (off+(orig+used+k)) <;> simp_all
  · intro h k hk
    simp [h k hk]

/-- Every source in an arbitrary private box is listed at most once per factor. -/
theorem count_le_length (fs : List Factor) : count fs ≤ fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih => cases f <;> simp [count] <;> omega

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable (rules : ∀ u : {u : N.Site // cell u = v}, Rule N u.val)

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "fs" => GridBoxes.factors N cell v siteID edgeID portID rules
local notation "wireChecks" => wiring N cell position pack width owner lane aligned edgeID portID channelID groupID v

/-- Actual integer bounds, including the two public capacities, for the cell's
physical work slab in each copy. -/
noncomputable def slab (capFine capReport : ℕ) (hf : GridBoxes.stride N cell v ≤ capFine)
    (hs : Fintype.card {u : N.Site // cell u = v} ≤ capReport) : Slab where
  guessed := guessedSize N cell v
  supplied := suppliedSize N cell v
  capFine := capFine
  incoming := incoming G v
  used := count fs
  capReport := capReport
  fineFits := hf
  reportFits := (count_le_length fs).trans (by simpa only [factors,List.length_map,siteList_length] using hs)

/-- One immutable private list for all copies of the box. -/
noncomputable def stored (capFine capReport : ℕ) : List Factor :=
  let orig := capFine+incoming G v
  stage orig fs ++ wireChecks capFine ++ reportZeros orig (count fs) capReport

private theorem stage_shift (off next : ℕ) (rows : List Factor) :
    ∀ f ∈ stage next rows, Factor.shift off f = f := by
  induction rows generalizing next with
  | nil => simp [stage]
  | cons r rows ih => cases r <;> exact List.forall_mem_cons.mpr ⟨rfl,ih _⟩

/-- All stored factors have only relative reads. Relocating the immutable
box to any final cell changes neither its bytes nor any source field. -/
theorem stored_shift (capFine capReport off : ℕ) :
    ∀ f ∈ stored N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v
      rules capFine capReport, Factor.shift off f = f := by
  simp only [stored,List.forall_mem_append]
  refine ⟨⟨stage_shift off _ fs,?_⟩,?_⟩
  · intro f hf
    have none := List.filterMap_eq_nil_iff.mp (wiring_tags N cell position pack width owner lane aligned
      edgeID portID channelID groupID v capFine) f hf
    cases f <;> simp_all [factorTag,Factor.shift]
  · intro f hf
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hf
    rfl

/-- The actual persistent bottom birth site, with one local work slab per copy.
The public layer has no information about the privately selected fine routes. -/
noncomputable def born (copies capFine capReport : ℕ) : Site :=
  let orig := capFine+incoming G v
  let stride := bottomStride orig capReport
  ⟨copies*stride, incoming (BottomRepeat.wide G copies) v,
    [stored N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules capFine capReport],
    [[.box 0 0 copies stride] ++ BottomRepeat.ties G channelID groupID v copies capFine stride]⟩

/-- At birth the complete public description uses only the single box record and
one row for each true cable or grouped port. -/
theorem born_rows (copies capFine capReport : ℕ) :
    (born N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
      copies capFine capReport).rows.length = 1+Fintype.card (BottomRepeat.Row G v) := by
  simp only [born,Site.rows,List.reverse_singleton,List.flatten_cons,List.flatten_nil,
    List.append_nil,List.singleton_append,List.length_cons,BottomRepeat.ties_length]
  exact Nat.add_comm _ _

/-- The private evaluator visits exactly the immutable stored list at each actual
copy stride, once, with no extra occurrence coming from its public word ties. -/
theorem born_occurrences (copies capFine capReport : ℕ) :
    let s := born N cell position pack width owner lane aligned siteID edgeID portID channelID groupID
      v rules copies capFine capReport
    let stride := bottomStride (capFine+incoming G v) capReport
    s.directory.occurrences = (List.range copies).flatMap (fun i =>
      (s.boxes[0]?.getD []).map fun f => (⟨f,i*stride,i⟩ : Occurrence)) := by
  intro s stride
  simp only [Directory.occurrences,Site.directory,s,Site.rows,born,List.reverse_singleton,List.flatten_cons,
    List.flatten_nil,List.append_nil,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.getD_eq_getElem?_getD,List.getElem?_cons_zero,Option.getD_some,Nat.zero_add]
  have discard {T : Type} (xs ys : List T) (h : ys = []) : xs ++ ys = xs := by simp [h]
  apply discard
  apply List.flatMap_eq_nil_iff.mpr
  intro r hr
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp hr
  rfl

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
