import OAI.LinearAlgebra.SpectralBooks.JointConvexity
import Mathlib.Analysis.Convex.Function

/-! # Joint convexity of tensor prices in a normed real spectral space -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open SiteTensor

/-- All placed tensor prices are jointly convex in a normed real vector space
with spectral prices. -/
theorem SpectralPlacementPrices.convexOn_price {K E : Type*} [Field K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : SpectralPlacementPrices K E)
    {I : Type} [Fintype I] (T : Raw.{0} I K) :
    ConvexOn ℝ Set.univ (P.price T) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have heq (u v : E) : a • u + b • v - u = b • (v-u) := by
    rw [show a = 1-b by linarith, sub_smul, one_smul, smul_sub]
    abel
  have heq' (u v : E) : a • u + b • v - v = a • (u-v) := by
    rw [show b = 1-a by linarith, sub_smul, one_smul, smul_sub]
    abel
  have h := P.price_le_of_common_fraction T x (a • x + b • y) y b
    ⟨hb, by linarith⟩ (fun i ↦ by
      rw [dist_eq_norm ((a • x + b • y) i)]
      change ‖a • x i + b • y i - x i‖ = b * dist (x i) (y i)
      rw [heq, norm_smul, Real.norm_of_nonneg hb, ← dist_eq_norm, dist_comm]) (fun i ↦ by
      rw [dist_eq_norm ((a • x + b • y) i)]
      change ‖a • x i + b • y i - y i‖ = (1-b) * dist (x i) (y i)
      rw [heq', norm_smul, Real.norm_of_nonneg ha, ← dist_eq_norm, show 1-b=a by linarith])
  simpa only [smul_eq_mul, show 1-b=a by linarith] using h

end SpectralBooks
end LinearAlgebra
end OAI
