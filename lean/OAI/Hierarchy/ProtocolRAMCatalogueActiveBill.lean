import OAI.Hierarchy.ProtocolRAMCatalogueOrdinal
import OAI.Hierarchy.TaggedWideActiveCost
import OAI.Hierarchy.ProtocolRAMCataloguePruning
import OAI.Hierarchy.ProtocolRAMBoughtLocations
import OAI.Hierarchy.ProtocolRAMCalendarOpeningBill

namespace OAI
/-! # Charging only activated physical rows in a padded original catalogue -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open AdaptiveProbe ProbeStage ProbeStage.Native ReportSockets CoreBoard ProtocolRAMEmit
open PurchaseFrozen PurchaseCT
open scoped BigOperators Classical
variable {h W k attempts : ℕ}

/-- The direct inequality needed by signed startup for the widths installed
in real catalogue slots. A positive relaxed rounding or disposable write in
a remaining padding slot only increases the full native length bill. -/
theorem installed_le_all {E : Type*} [Fintype E] {n : ℕ} (ordinal : E↪Fin n)
    (payload : ℕ) (bits : Fin n→ℕ) (len : Fin n→ℝ) (nonneg : ∀i,0≤len i) :
    (∑e,len (ordinal e)*((bits (ordinal e):ℝ)/payload))≤∑i,len i*((bits i:ℝ)/payload) := by
  let cost (i : Fin n) := len i*((bits i:ℝ)/payload)
  have eq := Finset.sum_map (s:=Finset.univ) ordinal cost
  change (∑e,cost (ordinal e))≤∑i,cost i
  rw [←eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>
    mul_nonneg (nonneg i) (by positivity))

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
