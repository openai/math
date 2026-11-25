import OAI.Hierarchy.ProbeCoreWalks
import OAI.Hierarchy.ProtocolRAMPurchaseInventory

namespace OAI
/-! # Range of the two physical stock prices on the original lane layout -/
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe
open scoped Classical
noncomputable section

/-- The static ROM uses exactly two types of bounding box. There is one
payload lane and there are two directional ends per stage and axis. -/
def routeCap (N : ℕ) (M : ℝ) (j : ℕ) : ℝ := if j=0 then (N:ℝ) else M+1

theorem routeCap_named (h d k : ℕ) (M : ℝ) (i : Commodity (Fin (2^h)) (CoreBoard.Stages h d) k) :
    routeCap (CoreBoard.Stages h d) M (PurchaseInventory.lane i)=CoreBoard.commodityLength M i := by
  rcases i with i|⟨⟨p,t⟩,l⟩
  · rfl
  · simp [routeCap,PurchaseInventory.lane,CoreBoard.commodityLength]

theorem routeCap_range {h d k : ℕ} (M : ℝ) (hm : 0≤M)
    (i : Commodity (Fin (2^h)) (CoreBoard.Stages h d) k) :
    routeCap (CoreBoard.Stages h d) M (PurchaseInventory.lane i) ∈
      Set.Icc 0 (max (CoreBoard.Stages h d:ℝ) (M+1)) := by
  rw [routeCap_named]
  cases i with
  | inl p => exact ⟨Nat.cast_nonneg _,le_max_left _ _⟩
  | inr p => exact ⟨by change 0≤M+1;linarith,le_max_right _ _⟩

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
