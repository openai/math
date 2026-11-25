import OAI.Computability.BorderVNP.PackedBottomRetainedCorePass
import OAI.Computability.BorderVNP.PackedGridSeedNativeNames

/-! # The original physical weighted-choice bundle at each actual prewired seed -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes GridPlacement BottomGridBank BottomReports Inherited Cover TeamContraction
open Diagonal.CellEntries Diagonal.ExternalSew DiagonalTallyCellReports ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (siteID : (W.routedFine position).Site ↪ Fin s) (edgeID : (W.routedFine position).Edge ↪ Fin m)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channelID : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groupID : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (c : Fin q → Deck (depth+2))

/-- Equality on physical deck coordinates for the routed source and box headers. -/
noncomputable local instance seedCoreDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
local notation3 "cap₀" => seedSiteCapacity n r q depth
local notation3 "width₀" => fun _ : Fin (GridHosts.tileCount q depth) => GridHosts.inputBlockWidth r n q depth
local notation3 "lane₀" => GridHosts.wiredLane G (GridHosts.tileCount q depth) Fintype.card_pos
local notation3 "pack₀" => routedPacking position W.route (fun _ => le_rfl)

/-- The actual native six-field header and original unstaged fine factors.
Its use choices are later read in the chronological native tape order. -/
noncomputable abbrev seedCoreBundle (slot base copies : ℕ) : BottomReports.Bundle :=
  ⟨W.seedUseHeader position c slot base copies,W.nativeFactors position code siteID edgeID portID c⟩

set_option maxHeartbeats 2000000 in
/-- The public birth record, complete private box including zero suffix, and
work/capacity metadata of the true prewired seed discharge the birth witness. -/
theorem seedCoreBundle_birth (slot base copies : ℕ) :
    (W.seedCoreBundle position code siteID edgeID portID c slot base copies).Birth
      (W.seedBorn position code siteID edgeID portID channelID groupID c copies) := by
  refine ⟨⟨wiring (W.routedFine position) (cell position W.route) position pack₀ width₀ order lane₀
    (W.seedLane_aligned position) edgeID portID channelID groupID c (3*cap₀),rfl⟩,?_,rfl,rfl,?_⟩
  · simp [seedBorn,BottomGridBank.born,Site.rows,seedUseHeader]
    exact Or.inl rfl
  · have hc := W.seedPositions_length position code siteID edgeID portID c
    rw [seedPositions,sidecarPositions,positions_length] at hc
    exact hc

/-- The canonical use block of this fixed prewire is exactly the list seen
by the native scanner of its full true stored box. -/
theorem seedCoreBundle_native (slot base copies : ℕ) (pre : List Bool) :
    List.ofFn ((W.seedCoreBundle position code siteID edgeID portID c slot base copies).useChoice pre) =
    List.ofFn (W.seedUseBundle position code siteID edgeID portID channelID groupID c slot base copies (lookup pre)).uses :=
  (W.seedCoreBundle position code siteID edgeID portID c slot base copies).useChoice_native pre
    (W.seedStored position code siteID edgeID portID channelID groupID c)

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
