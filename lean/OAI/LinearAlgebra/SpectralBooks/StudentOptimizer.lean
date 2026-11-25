import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! # Choice of heights in the Student bound -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- The finite height at which the coefficient of the linear term equals the load. -/
theorem exists_studentHeight {q : ℕ} (hq : 0 < q) {L m : ℝ} (hm : 0 < m)
    (hmL : m < L) :
    ∃ a : ℝ, 0 < a ∧ L * (1 + a⁻¹ ^ 2) ^ (-(q : ℝ) / 2) = m ∧
      Real.sqrt ((q : ℝ) + 1) / a =
        Real.sqrt (((q : ℝ) + 1) * ((L / m) ^ (2 / (q : ℝ)) - 1)) := by
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hratio : 1 < L / m := (one_lt_div hm).mpr hmL
  have hr : 0 < (L / m) ^ (2 / (q : ℝ)) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow hratio (by positivity))
  refine ⟨(Real.sqrt _)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hr), ?_, ?_⟩
  · rw [inv_inv, Real.sq_sqrt hr.le, add_sub_cancel, ← Real.rpow_mul (by linarith : 0 ≤ L/m)]
    have hpow : (2 / (q : ℝ)) * (-(q : ℝ) / 2) = -1 := by field_simp
    rw [hpow, Real.rpow_neg_one]
    field_simp [(hm.trans hmL).ne']
  · rw [div_inv_eq_mul, Real.sqrt_mul (by positivity : 0 ≤ (q : ℝ) + 1)]

end SpectralBooks
end LinearAlgebra
end OAI
