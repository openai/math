import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # The limiting threshold in the Student bound

The squared threshold for a fixed positive wire load tends to twice the natural
logarithm of the ratio of the log-rank to the load, as the flat dimension grows.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter
open scoped Topology

/-- The squared threshold in the Student tail bound tends to its Gaussian counterpart. -/
theorem tendsto_studentThreshold_sq {L m : ℝ} (hm : 0 < m) (hmL : m ≤ L) :
    Tendsto (fun d : ℕ ↦ (d : ℝ) * ((L / m) ^ (2 / ((d : ℝ) - 1)) - 1))
      atTop (𝓝 (2 * Real.log (L / m))) := by
  have hden : Tendsto (fun d : ℕ ↦ (d : ℝ) - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
  have hpos : 0 < L / m := div_pos (hm.trans_le hmL) hm
  have hderiv : HasDerivAt (fun x : ℝ ↦ (L / m) ^ (2 * x))
      (2 * Real.log (L / m)) 0 := by
    simpa [mul_comm] using
      (HasDerivAt.const_rpow hpos ((hasDerivAt_id (0 : ℝ)).const_mul 2))
  have hslope := hderiv.tendsto_slope_zero_right.comp (tendsto_inv_atTop_nhdsGT_zero.comp hden)
  have hfactor : Tendsto (fun d : ℕ ↦ 1 + ((d : ℝ) - 1)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_inv_atTop_zero.comp hden).const_add 1
  have h := hfactor.mul hslope
  rw [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with d hd
  have hd' : (d : ℝ) - 1 ≠ 0 := by exact_mod_cast (by omega : (d : ℤ) - 1 ≠ 0)
  simp only [Function.comp_apply, zero_add, inv_inv, mul_zero, Real.rpow_zero,
    smul_eq_mul, div_eq_mul_inv]
  field_simp
  ring

/-- Continuity of the square root gives convergence of the Student threshold itself. -/
theorem tendsto_studentThreshold {L m : ℝ} (hm : 0 < m) (hmL : m ≤ L) :
    Tendsto (fun d : ℕ ↦ Real.sqrt ((d : ℝ) * ((L / m) ^ (2 / ((d : ℝ) - 1)) - 1)))
      atTop (𝓝 (Real.sqrt (2 * Real.log (L / m)))) :=
  (tendsto_studentThreshold_sq hm hmL).sqrt

end SpectralBooks
end LinearAlgebra
end OAI
