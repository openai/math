import OAI.Computability.BorderVNP.ShortenEpochGeodesic

/-!
# Oriented midpoint segments in the product host

Normalize each factor speed by the full product distance. The resulting
tangent vector has norm one by the product metric formula and yields both
original endpoints at times `±dist/2`. Factors of speed zero need no angular
choice.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Finset

variable {I : Type*} [Fintype I]

/-- A factor with scalar speed follows its unit direction at exactly that speed,
including when the speed is zero. -/
theorem factor_speed (u : ℂ) (hu : ‖u‖ = 1) {m : ℝ} (hm : 0 ≤ m) (t : ℝ) :
    tangentLine (unitDirection (m • u)) (t * ‖m • u‖) = tangentLine u (t*m) := by
  have hn : ‖m • u‖ = m := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hm,hu,mul_one]
  rw [hn]
  rcases eq_or_lt_of_le hm with h | h
  · simp [← h, tangentLine]
  · have hne : m • u ≠ 0 := norm_pos_iff.mp (by rw [hn]; exact h)
    rw [unitDirection, ite_eq_right hne, hn, smul_smul, inv_mul_cancel₀ h.ne',one_smul]

/-- Every positive-length product segment admits exactly the oriented
midpoint presentation used by the motion and matching steps. -/
theorem exists_product_midpoint_line (a b : HyperbolicHost I) (hab : a ≠ b) :
    ∃ (c : HyperbolicHost I) (v : PiLp 2 fun _ : I => ℂ), ‖v‖ = 1 ∧
      shiftTo c (productLine v (-(dist a b / 2))) = a ∧
      shiftTo c (productLine v (dist a b / 2)) = b := by
  let R := dist a b
  have hR : 0 < R := dist_pos.mpr hab
  let d (i : I) := dist (a i) (b i)
  have hd (i : I) : 0 ≤ d i := dist_nonneg
  let speed (i : I) := d i / R
  have hs (i : I) : 0 ≤ speed i := div_nonneg (hd _) hR.le
  choose c u hu ha hb using (fun i => exists_factor_midpoint_line (a i) (b i))
  let v : PiLp 2 (fun _ : I => ℂ) := WithLp.toLp 2 fun i => speed i • u i
  have hnorm (i : I) : ‖v i‖ = speed i := by
    change ‖speed i • u i‖ = speed i
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hs i),hu,mul_one]
  have hscaled (i : I) : R/2 * speed i = d i/2 := by dsimp [speed]; field_simp
  refine ⟨WithLp.toLp 2 c, v, ?_, ?_, ?_⟩
  · apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [PiLp.norm_sq_eq_of_L2]
    simp_rw [hnorm, speed, div_pow]
    rw [← Finset.sum_div, ← host_dist_sq a b, div_self (pow_ne_zero _ hR.ne'), one_pow]
  · ext1 i
    change shiftFactor (c i) (tangentLine (unitDirection (speed i • u i))
      (-(R/2) * ‖speed i • u i‖)) = a i
    rw [factor_speed _ (hu i) (hs i), neg_mul, hscaled]
    exact ha i
  · ext1 i
    change shiftFactor (c i) (tangentLine (unitDirection (speed i • u i))
      ((R/2) * ‖speed i • u i‖)) = b i
    rw [factor_speed _ (hu i) (hs i), hscaled]
    exact hb i

end Epoch

end BorderVNP
end Computability
end OAI
