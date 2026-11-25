import OAI.Hierarchy.TaggedWideStack
import OAI.Hierarchy.TaggedWideReadoutPurchases

namespace OAI
/-! # Reindexing the purchased far compactor and its physical input pins -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open Tagged TaggedShorterPacking
open ThreeFlat Routing Spill TaggedShorterCompaction TaggedShorterNetwork
open scoped Classical BigOperators

/-- Each group has the same rectangular input neighborhood for the common far compactor. -/
theorem purchase_capacity (groups D half modules : ℕ) :
    TaggedShorterGroups.capacity (Fin groups) D half modules=max modules (groups*batches D half) := by
  simpa only [Fintype.card_fin] using Tagged.WideStack.capacity_eq (Fin groups) D half modules

namespace Purchased
variable {F : Type*} [Field F] {κ A bound : ℝ} {menu : WideMenu κ A} {x : WideParent κ A}
  {i : Fin menu.types} {S D M target : ℕ} (buy : Purchased F menu x i D S M bound)

def farAt (same : S=target) :
    Compactor F target M (Width (2^(menu.height i x)) (menu.height i x+menu.payload i x)) :=
  same ▸ buy.far

def readAt {V : Type} {width : ℕ} (same : S=target) (read : Input target D width→V) :
    Input S D width→V :=
  same.symm ▸ read

theorem cut_cast_closed {V : Type} [Fintype V] (same : S=target)
    (read : Input target D (menu.height i x+menu.payload i x)→V) (values : V→Bool) :
    (buy.cut (readAt same read)).closed values =
      (CutFormat.mk target D M (menu.height i x) (menu.payload i x) buy.near (buy.farAt same) read).closed values := by
  subst target
  rfl

end Purchased

end Hierarchy.ProbeStage.ReportSockets
end

end OAI
