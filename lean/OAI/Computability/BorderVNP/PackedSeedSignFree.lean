import OAI.Computability.BorderVNP.PackedSignFreeGrid
import OAI.Computability.BorderVNP.PackedGridSeedTape

/-! # The initial physical verifier batch stores only positive factors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes GridPlacement BottomGridBank BottomReports Inherited Cover TeamContraction
open Diagonal.CellEntries Diagonal.ExternalSew ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
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

/-- All private factors emitted by the prewired original seed bank at a genuine
Cayley cell, for any copy count, have a positive local observation. -/
theorem seedBorn_signFree (copies : ℕ) :
    (W.seedBorn position code siteID edgeID portID channelID groupID c copies).SignFree := by
  apply born_signFree

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
