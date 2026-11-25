import OAI.LinearAlgebra.SpectralBooks.RankLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Polynomial factors in tensor-power rank bounds -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open Filter MatrixMultiplication.Foundation
open scoped Topology

section

variable {F X Y Z : Type*} [Field F] [Fintype X] [Fintype Y]

/-- A polynomial overhead in a uniform tensor-power algorithm disappears
on taking the asymptotic rank. -/
theorem asymptoticRank_le_of_polynomial_power_bound (T : Tensor F X Y Z) (r D : ℕ)
    (h : ∀ n : ℕ, tensorRank (Tensor.power T n) ≤ (n + 1)^D * r^n) :
    asymptoticRank T ≤ r := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa [Function.comp_def] using (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hpoly : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ ((D : ℝ) / n)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using
      (tendsto_rpow_div_mul_add D 1 (-1) zero_ne_one).comp hbase
  have hlim := hpoly.mul_const (r : ℝ)
  rw [one_mul] at hlim
  apply le_of_tendsto_of_tendsto (tendsto_tensorRank_power_root T) hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hcast : (tensorRank (Tensor.power T n) : ℝ) ≤ ((n : ℝ) + 1)^D * (r : ℝ)^n := by
    exact_mod_cast h n
  calc
    _ ≤ (((n : ℝ) + 1)^D * (r : ℝ)^n) ^ (n : ℝ)⁻¹ :=
      Real.rpow_le_rpow (by positivity) hcast (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.pow_rpow_inv_natCast (by positivity) hn.ne',
        ← Real.rpow_natCast_mul (by positivity), div_eq_mul_inv]

end

end

end SpectralBooks
end LinearAlgebra
end OAI
