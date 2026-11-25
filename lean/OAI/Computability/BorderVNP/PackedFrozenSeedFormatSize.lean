import OAI.Computability.BorderVNP.PackedFrozenSeedInitial
import OAI.Computability.BorderVNP.PackedFrozenRowCapacity

/-! # The size of the initial immutable row directory

A grouped tile has one box, one port and at most two incidence rows for each
direction. The bottom rectangle counts one site and one cable for each
tile and direction respectively. Thus twice its physical row count suffices,
including when a directed edge loops back to its starting tile.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover BorderVNP.Epoch Packing Packing.DeckGrid Packing.Inherited
open Packing.Inherited.FrozenTape Diagonal.ExternalSew Diagonal.ExternalSew.RowTrace
open TeamContraction ParseBatch ParseBatchVerifier Prewire TeamScales
open scoped Classical BorderVNP.Epoch.Cube

variable {D n r d teams time pins link inner : ℕ} {Edge : Type}
    (G : Wiring teams r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (copies : ℕ)

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "w" => 60*logWidth r n
local notation "P₀" => physicalRows (SelectedSchedule.bottom (D := D) (d+1))
local notation3 "fmt" => seedFormat G order position copies
local notation3 "channels" => (groupedGridRows G axes d order position copies).edge
local notation3 "groups" => (Equiv.refl (Fin tiles)).toEmbedding
local notation3 "rs₀" => Seed.rows n r order position channels groups copies

private theorem bottom_count :
    tiles*(2+2*Fintype.card (Direction axes)) = 2*P₀ := by
  simp only [physicalRows, SelectedSchedule.bottom, Shortening.PublicCapacity.gridShape,
    GridHosts.tileCount, CoverScale.sites, Fintype.card_fun, Fintype.card_fin]
  ring

/-- Two physical rectangles hold every reserved public row of the actual birth format. -/
theorem seedFormat_rows : Fintype.card (fmt).Rows ≤ 2*P₀ := by
  have h : Fintype.card (fmt).Rows = Fintype.card (Bottom.Row rs₀ 0) := Fintype.card_congr (Equiv.refl _)
  rw [h]
  simpa only [Nat.add_zero, bottom_count] using
    Seed.row_slots n r order position channels groups copies 0

/-- Every real row contributes at most nine scalar words of the common width. -/
theorem seedFormat_payload : Fintype.card (fmt).Payload ≤ 2*P₀*9*w := by
  have h : Fintype.card (fmt).Payload = Fintype.card (Bottom.Payload rs₀ 0 w) := Fintype.card_congr (Equiv.refl _)
  rw [h]
  simpa only [bottom_count] using
    Seed.payload_slots n r order position channels groups copies 0 w

/-- Full pin count at any chosen owner width, including active flags and all scalar bits. -/
theorem seedFormat_pins (ownerWidth : ℕ) :
    Fintype.card (FrozenTape.Pins (fmt).Rows (fmt).Payload ownerWidth) ≤ 2*P₀*(1+ownerWidth+9*w) := by
  have h : Fintype.card (FrozenTape.Pins (fmt).Rows (fmt).Payload ownerWidth) =
      Fintype.card (FrozenTape.Pins (Bottom.Row rs₀ 0) (Bottom.Payload rs₀ 0 w) ownerWidth) :=
    Fintype.card_congr (Equiv.refl _)
  rw [h]
  have count := Seed.pin_count n r order position channels groups copies 0 w ownerWidth
  simp only [Nat.add_zero, bottom_count] at count
  exact count.trans_eq (by ring)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
