import OAI.Computability.BorderVNP.PackedSeedBornCompilerFields
import OAI.Computability.BorderVNP.PackedSeedSignFree
import OAI.Computability.BorderVNP.PackedInheritedPlacementBoxes
import OAI.Computability.BorderVNP.PackedBottomWiredSite
import OAI.Computability.BorderVNP.PackedBottomBoxLocality

/-! # Guard conditions at the actual original signed verifier banks -/

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
    {K : Type*} [Field K] {b : ℕ} (e : PaidIdentity K D b)

/-- Equality of the finite deck positions used in the prewired batch's physical bank. -/
noncomputable local instance seedGuardDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
local notation3 "V₀" => GridHosts.tileCount q depth
local notation3 "width₀" => fun _ : Fin V₀ => GridHosts.inputBlockWidth r n q depth
local notation3 "lane₀" => GridHosts.wiredLane G V₀ Fintype.card_pos
local notation3 "pack₀" => routedPacking position W.route (fun _ => le_rfl)
local notation3 "S₀" => seedSiteCapacity n r q depth
local notation3 "K₀" => seedBoxCapacity n r q depth (Fintype.card (Direction q))
local notation3 "rules₀" => fun v => W.routedRules position (sidecarReport code) (Subtype.val v)

/-- The actual sparse original-site program is local and has only relative
box operands; the finite addresses in the cell can therefore be relocated. -/
theorem seedBorn_guard (copies : ℕ) :
    let a := W.seedBorn position code siteID edgeID portID channelID groupID c copies
    a.Local ∧ a.RelativeBoxes := by
  intro a
  constructor
  · exact born_local (W.routedFine position) (cell position W.route) position pack₀ width₀ order lane₀
      (W.seedLane_aligned position) siteID edgeID portID channelID groupID c rules₀ (3*S₀) S₀ copies
      (W.seed_stride_le position c) (W.seedSlab position code siteID edgeID portID c).reportFits
  · exact born_relative (W.routedFine position) (cell position W.route) position pack₀ width₀ order lane₀
      (W.seedLane_aligned position) siteID edgeID portID channelID groupID c rules₀ copies (3*S₀) S₀

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
