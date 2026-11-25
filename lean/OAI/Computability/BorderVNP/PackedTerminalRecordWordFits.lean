import OAI.Computability.BorderVNP.PackedFinalCellFields
import OAI.Computability.BorderVNP.PackedHistorySewnTagModels
import OAI.Computability.BorderVNP.FiniteSewnFieldScalarBounds

/-! # Operand bounds of the actual signed sewn and relocated records -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Crossing Inherited Diagonal.ExternalSew
open scoped Classical

variable {D ae ap be bp : ℕ} {A P U Free Cable : Type}
    [Fintype A] [Fintype P] [Fintype U] [Fintype Cable]
    {width : A → ℕ} (N : Network D A width) (lane : P ↪ Σ a, Fin (width a))
    {cw : Cable → ℕ} (B : Bundle (FineView.layout N lane) Free Cable cw)
    (gw : U → ℕ) (freeLane : Free ↪ Σ u, Fin (gw u)) (owner : U → N.Site)
    (aligned : ∀ f, owner (freeLane f).1 = B.layout.attach f)
    (oldEdge : N.Edge ↪ Fin ae) (oldPort : A ↪ Fin ap)
    (edge : (N.Edge ⊕ Cable) ↪ Fin be) (port : U ↪ Fin bp) (old : Site.Programs N)

local notation3 (prettyPrint := false) "live" => sewnPrograms N lane B gw freeLane owner aligned oldEdge oldPort edge port old
local notation3 (prettyPrint := false) "read" => sewnRead N lane B gw freeLane owner aligned oldEdge oldPort edge port

/-- Public scalar magnitudes of a signed clipped or copied interval are
bounded by the actual staged extent and the predecessor's operands. -/
theorem sewnPrograms_scalarBound (v : N.Site) {bound : ℕ} (prior : (old v).program.ScalarBound bound) :
    (live v).program.ScalarBound (max bound (max 1 (live v).program.size)) := by
  let f := read v ∘ Fin.cast (old v).size
  exact stage_scalarBound (old v).program prior (intervals f) f (intervals_cover f)

end Packing.SewnField

namespace Packing.Inherited.FinalCell

open Crossing CellSparse CellAddresses InheritedBank BankBoxOrdinal
open private off from OAI.Computability.BorderVNP.PackedBankSortedCell
open scoped Classical

variable {D s n p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin n)
  (portID : P ↪ Fin p) (owner : Fin s → ℕ) (state : N.Site → Site)

/-- A field bound valid for every record of the final sparse directory. Its
three terms are the actual assignment stack, the global number of boxes
and a bound on the unrelocated local scalars. Arbitrary reported counts do
not affect the set of records. -/
theorem packet_recordFields (ho : ∀ v, owner (siteID v) = cell v)
    (incoming_eq : ∀ v, (state v).incoming = incoming N v)
    {scalar boxes : ℕ} (localFields : ∀ v, (state v).ScalarBound scalar)
    (boxBound : (∑ i, (slots siteID (fun v => (state v).boxes) i).length) ≤ boxes)
    (c : ℕ) (reports : List (List ℕ)) :
    ∀ r ∈ (directory owner N cell siteID edgeID portID state c reports).records,
      Packet.RecordFields r (max (countBase N cell state c) boxes+scalar+1) := by
  intro r hr
  obtain ⟨v,hv,placed⟩ := List.mem_flatMap.mp hr
  have atCell : cell v = c := (ho v).symm.trans (site_owner siteID owner hv)
  rcases List.mem_append.mp placed with hr | ht
  · have start := siteBase_fits N cell (cell v) siteID (fun u => (state u).size) ⟨v,rfl⟩
    have bit : off N cell siteID state v ≤ countBase N cell state c := by
      change off N cell siteID state v+(state v).size ≤ privateBits N cell state (cell v) at start
      change off N cell siteID state v ≤ privateBits N cell state c+_
      rw [atCell] at start
      omega
    have box : firstBox siteID owner state v ≤ boxes := by
      apply le_trans _ boxBound
      unfold firstBox base
      exact Finset.sum_le_sum (fun i _ => by split <;> simp)
    exact ((state v).placed_recordFields (localFields v) _ _ _ hr).mono
      ((Nat.add_le_add_right (max_le_max bit box) scalar).trans (Nat.le_succ _))
  · have wire := Placement.ties_recordFields N cell (cell v) siteID edgeID portID state ⟨v,rfl⟩
      (incoming_eq v) r ht
    change Packet.RecordFields r (countBase N cell state (cell v)+1) at wire
    rw [atCell] at wire
    exact wire.mono (Nat.succ_le_succ ((le_max_left ..).trans (Nat.le_add_right _ _)))

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
