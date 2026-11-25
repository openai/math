import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! # Euclidean error in a streamed phase diagonal

The input is the represented vector at the beginning of the layer. Coefficient
errors scale with its Euclidean norm, whereas scalar rounding errors accrue in
quadrature over the array.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

variable {ι : Type*} [Fintype ι]

/-- Exact streamed multiplication by unit-modulus entries as a linear
isometry of the padded array. -/
noncomputable def phaseLayerIsometry (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ ι where
  toFun x := WithLp.toLp 2 (fun i => c i * x i)
  map_add' x y := by ext i; exact mul_add _ _ _
  map_smul' r x := by ext i; exact mul_left_comm _ _ _
  norm_map' x := by
    change ‖(WithLp.toLp 2 (fun i => c i * x i) : EuclideanSpace ℂ ι)‖ = ‖x‖
    simp only [EuclideanSpace.norm_eq, norm_mul, hc, one_mul]

/-- Evaluation on a single address does not change its stored index. -/
@[simp] theorem phaseLayerIsometry_apply (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1)
    (x : EuclideanSpace ℂ ι) (i : ι) : phaseLayerIsometry c hc x i = c i * x i := rfl

/-- Uniform per-record errors in a complex array accumulate in quadrature. -/
theorem euclidean_norm_le_of_coordinates (z : EuclideanSpace ℂ ι) {u : ℝ}
    (hu : 0 ≤ u) (h : ∀ i, ‖z i‖ ≤ u) :
    ‖z‖ ≤ Real.sqrt (Fintype.card ι) * u := by
  apply le_of_sq_le_sq _ (by positivity)
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt (by positivity)]
  calc
    ∑ i, ‖z i‖ ^ 2 ≤ ∑ _i : ι, u ^ 2 :=
      Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) _
    _ = _ := by simp

/-- Coordinatewise relative errors carry no dimension-dependent factor in ℓ². -/
theorem euclidean_norm_le_mul_of_coordinates (z x : EuclideanSpace ℂ ι) {u : ℝ}
    (hu : 0 ≤ u) (h : ∀ i, ‖z i‖ ≤ u * ‖x i‖) :
    ‖z‖ ≤ u * ‖x‖ := by
  apply le_of_sq_le_sq _ (by positivity)
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (h i) 2

/-- Apply a diagonal to represented inputs, including a uniform absolute error
in its streamed coefficients and a uniform rounding error on every output. -/
theorem phaseLayer_error_le (c c' : ι → ℂ) (x y : EuclideanSpace ℂ ι)
    {u M : ℝ} (hu : 0 ≤ u) (hx : ‖x‖ ≤ M)
    (hc : ∀ i, ‖c' i - c i‖ ≤ u) (hy : ∀ i, ‖y i - c' i * x i‖ ≤ u) :
    ‖y - WithLp.toLp 2 (fun i => c i * x i)‖ ≤
      u * (M + Real.sqrt (Fintype.card ι)) := by
  let ideal : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => c i * x i)
  let approx : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => c' i * x i)
  have hround : ‖y - approx‖ ≤ Real.sqrt (Fintype.card ι) * u :=
    euclidean_norm_le_of_coordinates _ hu hy
  have hcoef : ‖approx - ideal‖ ≤ u * ‖x‖ := by
    apply euclidean_norm_le_mul_of_coordinates _ _ hu
    intro i
    change ‖c' i * x i - c i * x i‖ ≤ u * ‖x i‖
    rw [← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)
  calc
    ‖y - ideal‖ ≤ ‖y - approx‖ + ‖approx - ideal‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.sqrt (Fintype.card ι) * u + u * M :=
      add_le_add hround (hcoef.trans (mul_le_mul_of_nonneg_left hx hu))
    _ = _ := by ring

/-- The working precision of the multiplication algorithm meets the local
layer allowance on the whole padded array. -/
theorem phaseLayer_dyadic_error_le {k : ℕ} (hk : 1 ≤ k)
    (hcard : Fintype.card ι = 2 ^ k) (c c' : ι → ℂ) (x y : EuclideanSpace ℂ ι)
    (hx : ‖x‖ ≤ (2 : ℝ) ^ (13*k))
    (hc : ∀ i, ‖c' i - c i‖ ≤ ((2 : ℝ) ^ (70*k))⁻¹)
    (hy : ∀ i, ‖y i - c' i * x i‖ ≤ ((2 : ℝ) ^ (70*k))⁻¹) :
    ‖y - WithLp.toLp 2 (fun i => c i * x i)‖ ≤ ((2 : ℝ) ^ (50*k))⁻¹ := by
  apply (phaseLayer_error_le c c' x y (by positivity) hx hc hy).trans
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat, inv_mul_le_iff₀ (by positivity)]
  have hs : Real.sqrt ((2 : ℝ)^k) ≤ (2 : ℝ)^(13*k) :=
    (Real.sqrt_le_self_iff.mpr (.inr (one_le_pow₀ (by norm_num)))).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  calc
    (2 : ℝ)^(13*k) + Real.sqrt (2^k) ≤ 2^(13*k) + 2^(13*k) := by gcongr
    _ = 2^(13*k+1) := by rw [pow_succ]; ring
    _ ≤ 2^(20*k) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ = 2^(70*k) * ((2 : ℝ)^(50*k))⁻¹ := by
      rw [show 70*k = 20*k + 50*k by omega, pow_add]
      field_simp

end NearSquareRoot
end Computability
end OAI
