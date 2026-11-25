import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! # Limiting the two exterior relocation bounds

The adjacent exterior levels contribute opposite slopes to the normalized
log prices of the creation-first and contraction-first restrictions. With the
slope chosen from the endpoint prices, the two limits agree.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Real
open scoped Topology

/-- Divide the ordinary two-summand bound by the power and pass to its limit.
Here `plus` and `minus` are the base-two logs of the two adjacent level ratios. -/
theorem relocation_le_of_ratio_limits {wA wB wC u d c slope : ℝ}
    (plus minus : ℕ → ℝ)
    (hplus : Tendsto (fun n : ℕ ↦ plus n / n) atTop (𝓝 slope))
    (hminus : Tendsto (fun n : ℕ ↦ minus n / n) atTop (𝓝 (-slope)))
    (hbound : ∀ᶠ n : ℕ in atTop, (n : ℝ) * wC ≤ c +
      max (n * wB + ((1 - u) * d) * plus n) (n * wA + (u * d) * minus n)) :
    wC ≤ max (wB + ((1 - u) * d) * slope) (wA + (u * d) * (-slope)) := by
  have hl := (tendsto_const_div_atTop_nhds_zero_nat c).add <|
    ((hplus.const_mul ((1 - u) * d)).const_add wB).max
      ((hminus.const_mul (u * d)).const_add wA)
  rw [zero_add] at hl
  refine ge_of_tendsto hl ?_
  filter_upwards [eventually_gt_atTop 0, hbound] with n hn h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  change wC ≤ c / n + max (wB + ((1 - u) * d) * (plus n / n)) (wA + (u * d) * (minus n / n))
  apply (mul_le_mul_iff_of_pos_right hn').mp
  rw [add_mul, max_mul_of_nonneg _ _ hn'.le]
  convert h using 1 <;> field_simp

/-- A price difference of at most `d * logb 2 q` is realized by a slope
`logb 2 q * s` with `s ∈ [-1,1]`. Using these levels makes both branches
converge to the linear interpolation of the endpoint prices. -/
theorem relocation_le_of_two_bounds {wA wB wC u d c : ℝ} {q : ℕ}
    (hd : 0 < d) (hq : 2 ≤ q)
    (hmove : |wA - wB| ≤ d * logb 2 q)
    (hbranches : ∀ s : ℝ, s ∈ Set.Icc (-1) 1 → ∃ plus minus : ℕ → ℝ,
      Tendsto (fun n : ℕ ↦ plus n / n) atTop (𝓝 (logb 2 q * s)) ∧
      Tendsto (fun n : ℕ ↦ minus n / n) atTop (𝓝 (-(logb 2 q * s))) ∧
      ∀ᶠ n : ℕ in atTop, (n : ℝ) * wC ≤ c +
        max (n * wB + ((1 - u) * d) * plus n) (n * wA + (u * d) * minus n)) :
    wC ≤ (1 - u) * wA + u * wB := by
  have hlog : 0 < logb 2 q := Real.logb_pos (by norm_num) (by exact_mod_cast lt_of_lt_of_le Nat.one_lt_two hq)
  have hden := mul_pos hd hlog
  let s := (wA - wB) / (d * logb 2 q)
  have hs : s ∈ Set.Icc (-1) 1 := by
    have h := abs_le.mp hmove
    exact ⟨(le_div_iff₀ hden).mpr (by linarith), (div_le_iff₀ hden).mpr (by linarith)⟩
  obtain ⟨plus, minus, hplus, hminus, h⟩ := hbranches s hs
  have hbal : d * logb 2 q * s = wA - wB := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hden.ne'
  apply (relocation_le_of_ratio_limits plus minus hplus hminus h).trans
  apply max_le <;> linarith only [hbal, congrArg (u * ·) hbal]

end SpectralBooks
end LinearAlgebra
end OAI
