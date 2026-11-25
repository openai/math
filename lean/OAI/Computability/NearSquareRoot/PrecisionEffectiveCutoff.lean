import OAI.Computability.NearSquareRoot.PrecisionEffectiveBudget
import OAI.Computability.NearSquareRoot.PrecisionEffectiveExtent
import OAI.Computability.NearSquareRoot.PrecisionGroupedAccuracy

/-! # Effective admissibility and accuracy of the grouped Walsh transform

A single computable cutoff applies to every input, every selected width and
every node of the recursive computation using the specified template.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open KernelPass PhysicalWalshNode

theorem grouped_accurate_of_cutoff {a W M k : ℕ} (ha : 1 < a+1) (hw : 0 < W)
    (plan : Plan (a+1) W W) (hp : Correct plan) (hC : recursionFactor plan ≤ M)
    (hk : precisionCutoff M ≤ k) : GroupedAccurateAt ha hw plan k := by
  have pos := (precisionCutoff_pos M).trans_le hk
  have hW := (width_le_recursionFactor plan).trans hC
  have budget := (Nat.mul_le_mul_left (Nat.log 2 k+1) hW).trans (half_budget_of_cutoff hk)
  exact grouped_accurate_of_even ha hw plan pos (even_accurate_of_bounds ha hw plan pos
    (run_good_of_allowance hw plan hp pos (depth_allowance_of_cutoff hC hk))
    (fun _ hs => extent_le_of_half_budget ha hw pos hs budget))

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
