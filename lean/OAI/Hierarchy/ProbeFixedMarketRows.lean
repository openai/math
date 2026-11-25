import OAI.Hierarchy.ProbeFixedNativeBoards
import OAI.Hierarchy.ProtocolRAMCalendarStripTreeBudget

namespace OAI
/-! # Exact row count of the padded marketplace -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "fm" => v.nativeFormats P z width
local notation "bs" => v.nativeBoards P z width
local notation "rowFactor" => StripChart.treeRowsFactor (2^v.W) k v.sampler.degree v.depth

theorem discrepancy_scan_rows (a : Attempt) : (fm a).market.failures.rows=rowFactor*2^z := by
  have total : (fm a).market.rows=PurchaseFrozen.count z (2^v.W) k*PurchaseFrozen.paths z v.sampler.degree v.depth :=
    candidate_count F v.mesh (v.privateArena P z width) P.joint.initial bs a
  have shape : (fm a).market.failures.rows=(fm a).market.rows := by cases a <;> rfl
  rw [shape,total,PurchaseFrozen.count_eq]
  change ((2*rounds (2^v.W)+1)*(2*k))*PurchaseFrozen.paths z v.sampler.degree v.depth=rowFactor*2^z
  unfold StripChart.treeRowsFactor PurchaseFrozen.paths
  ac_rfl

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
