import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OAI
/-! # Choosing the index for bounded-degree amplification -/

namespace ThreeFlat.Expander

open Filter Topology

/-- At arbitrarily late indices, the factor `3^j` absorbs both terms in
the bound for the graph of ports. -/
theorem exists_amplification_index {α C : ℝ} (hα : 0 < α) (h3 : α < 3)
    (_hC : 0 ≤ C) (j₀ : ℕ) :
    ∃ j ≥ j₀, 3456 * max 1 (C * α^j) ≤ (3 : ℝ)^j / 8 := by
  have decay (a c : ℝ) (ha : 0 ≤ a) (ha3 : a < 3) :
      ∀ᶠ j : ℕ in atTop, 3456 * (c * a^j) ≤ (3 : ℝ)^j / 8 := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg ha (by norm_num : (0:ℝ) ≤ 3))
      ((div_lt_one (by norm_num : (0:ℝ) < 3)).mpr ha3)
    have hlim : Tendsto (fun j : ℕ => (27648*c) * (a/3)^j) atTop (𝓝 0) := by
      simpa using hp.const_mul (27648*c)
    filter_upwards [hlim.eventually_lt_const (by norm_num : (0:ℝ) < 1)] with j hj
    have hsmall : (27648 * c * a^j) / (3:ℝ)^j < 1 := by
      simpa only [div_pow, ← mul_div_assoc] using hj
    have hlt := (div_lt_one (by positivity : (0:ℝ) < 3^j)).mp hsmall
    linarith
  have both : ∀ᶠ j : ℕ in atTop,
      j₀ ≤ j ∧ 3456 * max 1 (C * α^j) ≤ (3:ℝ)^j / 8 := by
    filter_upwards [eventually_ge_atTop j₀, decay 1 1 zero_le_one (by norm_num),
      decay α C hα.le h3] with j hj hone hpow
    refine ⟨hj, ?_⟩
    rcases le_total 1 (C * α^j) with h | h
    · rwa [max_eq_right h]
    · simpa [max_eq_left h] using hone
  exact both.exists

end ThreeFlat.Expander

end OAI
