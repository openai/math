import OAI.Hierarchy.ProtocolRAMCalendarInstalledCharge

namespace OAI
/-! # An installed strip is charged at its direct, tree and stock prices -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe RepairHistogram PurchaseStage
open scoped Classical BigOperators

/-- Only positive native widths need a price comparison, so an inactive padded
record has no geometric readback obligation. -/
theorem charges_install_mono {w n rows goods p q : ℕ} (B : CashColumns) (m : Memory w)
    (payload copies : ℕ) (cost rate : Fin n→ℝ) (tree treeRate : Fin rows→ℝ)
    (route allowance : Fin goods→ℝ) (opening : Fin p→ℝ) (other : Fin q→ℝ)
    (priced : ∀i,(m (B.direct+i.val)).val≠0 → cost i≤rate i)
    (forest : ∀i,(m (B.broadcast+i.val)).val≠0 → tree i≤treeRate i)
    (spill : ∀i,(m (B.excess+i.val)).val≠0 → route i≤allowance i) :
    (charges B n rows goods p m payload copies cost tree route opening).install ≤
      (charges B n rows goods q m payload copies rate treeRate allowance other).install := by
  unfold charges
  refine add_le_add (add_le_add (div_le_div_of_nonneg_right (Finset.sum_le_sum ?_) (Nat.cast_nonneg _))
    (div_le_div_of_nonneg_right (Finset.sum_le_sum ?_) (Nat.cast_nonneg _))) (Finset.sum_le_sum ?_)
  · intro i _
    by_cases dead : (m (B.direct+i.val)).val=0
    · simp [dead]
    · exact mul_le_mul_of_nonneg_left (priced i dead) (Nat.cast_nonneg _)
  · intro i _
    by_cases dead : (m (B.broadcast+i.val)).val=0
    · simp [dead]
    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (forest i dead) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · intro i _
    by_cases dead : (m (B.excess+i.val)).val=0
    · simp [dead]
    · exact mul_le_mul_of_nonneg_left (spill i dead) (by positivity)

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
