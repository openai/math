import OAI.Hierarchy.Catalyst

namespace OAI
/-! # Changing the length unit for an arbitrary spectral price -/

noncomputable section
namespace Hierarchy.GridLens

open LinearAlgebra.SpectralBooks SiteTensor
open scoped BigOperators

variable {F : Type*} [Field F] {k : ℕ}
private abbrev Space (k : ℕ) := EuclideanSpace ℝ (Fin k)

private theorem dilation_dist (R : ℝ) (pos : 0 < R) (x y : Space k) :
    R * dist (R⁻¹ • x) (R⁻¹ • y) = dist x y := by
  rw [dist_smul₀, Real.norm_of_nonneg (inv_nonneg.mpr pos.le), ← mul_assoc,
    mul_inv_cancel₀ pos.ne',one_mul]

/-- Multiply the price and metric by the lens radius, expressing the resulting
metric in the original Euclidean coordinates. -/
def rescale (P : SpectralPlacementPrices F (Space k)) (R : ℝ) (pos : 0 < R) :
    SpectralPlacementPrices F (Space k) where
  price T x := R * P.price T (fun i => R⁻¹ • x i)
  zero_tensor T h x := by rw [P.zero_tensor T h,mul_zero]
  collapsed T x := by rw [P.collapsed,mul_zero]
  group T f x := congrArg (R * ·) (P.group T f (fun i => R⁻¹ • x i))
  wire x := by rw [P.wire]; exact dilation_dist R pos _ _
  transport T x y := by
    have h := mul_le_mul_of_nonneg_left
      (P.transport T (fun i => R⁻¹ • x i) (fun i => R⁻¹ • y i)) pos.le
    rw [Finset.mul_sum] at h
    simp_rw [← mul_assoc, dilation_dist R pos] at h
    simpa only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos pos] using h
  dist_le_diagonal x i j := by
    simpa only [dilation_dist R pos] using mul_le_mul_of_nonneg_left
      (P.dist_le_diagonal (fun i => R⁻¹ • x i) i j) pos.le
  normalized x := by
    let y := x.trans
      (⟨fun t => R⁻¹ • t, fun a b h => by
        have := congrArg (R • ·) h
        simpa only [smul_smul,mul_inv_cancel₀ pos.ne',one_smul] using this⟩ :
      Space k ↪ Space k)
    obtain ⟨s,hs⟩ := P.normalized y
    refine ⟨s,fun T nz => ?_⟩
    change R * P.price T y = (R * P.price _ y) * _
    rw [hs T nz, mul_assoc]

theorem rescale_price {I : Type} [Fintype I] (P : SpectralPlacementPrices F (Space k))
    (R : ℝ) (pos : 0<R) (T : Raw.{0} I F) (x : I → Space k) :
    (rescale P R pos).price T (fun i => R • x i) = R * P.price T x := by
  simp [rescale,smul_smul,inv_mul_cancel₀ pos.ne']


end Hierarchy.GridLens

end
end OAI
