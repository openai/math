import OAI.Computability.BorderVNP.DiagonalBottomBundlePowerRead
import OAI.Computability.BorderVNP.CubePhysicalGridReportSlots

/-! # The actual retained bottom host of a numbered unary occurrence -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.Tracked

open Crossing

/-- A genuine equality of physical layouts transports each power-slot host
by the equality induced on site types. -/
theorem castLayout_power_site {D exp : ℕ} {P Team Param Gadget : Type} [Fintype Team] [Fintype Param]
    {bits : P → ℕ} {N M : Network D P bits} (h : N = M)
    (t : Tracked Team Param Gadget exp N) (w : PowerSlot Team Param exp) :
    (t.castLayout h).words.site w = Eq.mp (congrArg Network.Site h) (t.words.site w) := by
  subst M
  rfl

end Diagonal.CellEntries.Tracked

namespace Packing.DeckGrid.WiredWitness

open Crossing Diagonal.CellEntries Cover TeamContraction ParseBatch ParseBatchVerifier
open GridPlacement Prewire Diagonal.ExternalSew.GridHosts VPVNP VPVNP.ParseGrammar
open scoped Classical
set_option maxHeartbeats 1200000

variable {R r pins link n D q depth t inner g : ℕ} {Edge Gadget : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {state : Fin g}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- The grouped and repeated seed puts the chosen slot at its genuine original
routed fine cell, independently of the hidden wires, leaf and bundle copy. -/
theorem bundle_power_site {copies : ℕ} (z : Fin copies → W.Hidden position) (i : Fin copies)
    (u : WeightSites n g r d) :
    (W.bundle (Gadget := Gadget) position copies z).words.site ((i,()),u) = cell position W.route (W.routedPowerSite position u) := by
  let original := W.seedGrid_eq position
  let t : Tracked Unit _ Gadget _ (W.seedGrid position) := ⟨W.seedTags position (z i),W.seedWords position (z i)⟩
  exact (Tracked.castLayout_power_site original t ((),u)).trans rfl

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
