import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Selector costs for the shortening from a border identity

In Lemma 3.3 the same fixed-width selector is sent from the center to each
of the `2 * D` terminals. A polynomial number of basis tensors, followed by
expansion of each tensor into at most `L ^ t` words, contributes only a
vanishing overhead per copy beyond the cost `2 * D * log₂ L`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open Filter
open scoped Topology

/-- The stars-and-bars bound for degree-`t` basis terms is polynomial in `t`
for fixed positive coordinate dimension. -/
theorem basisCount_le_polynomial (t v : ℕ) (hv : 0 < v) :
    (t + v - 1).choose (v - 1) ≤ (t + 1) ^ v := by
  calc
    _ ≤ (t + v - 1 + 1 - (v - 1)) ^ (v - 1) := Nat.choose_le_sub_pow _ _
    _ = (t + 1) ^ (v - 1) := by congr 1; omega
    _ ≤ (t + 1) ^ v := Nat.pow_le_pow_right (by omega) (by omega)

/-- The equivalent degree-first count supplied by the span of tensor powers. -/
theorem powersCount_le_polynomial (v t : ℕ) (hv : 0 < v) :
    (v + t - 1).choose t ≤ (t + 1) ^ v := by
  rw [← Nat.choose_symm (show t ≤ v + t - 1 by omega),
    show v + t - 1 - t = v - 1 by omega, Nat.add_comm v t]
  exact basisCount_le_polynomial t v hv

/-- Number of selector bits for the expanded words, including the final
rounding to an integral cable width. -/
theorem selectorWidth_le (t v L : ℕ) (hL : 0 < L) :
    (Nat.clog 2 ((t + 1) ^ v * L ^ t) : ℝ) ≤
      v * Real.logb 2 (t + 1) + t * Real.logb 2 L + 1 := by
  let A := (t + 1) ^ v * L ^ t
  have hA : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr (by dsimp [A]; positivity)
  have hceil := (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : 1 < (2 : ℝ))
    (show 1 ≤ (A : ℝ) by exact_mod_cast hA))).le
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.natCeil_logb_natCast] at hceil
  simpa [A, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.logb_mul
    (by positivity : (((t : ℝ) + 1) ^ v) ≠ 0) (by positivity : ((L : ℝ) ^ t) ≠ 0),
    Real.logb_pow] using hceil

/-- Per-copy logarithmic and rounding overhead tends to zero even with a
selector running separately to every terminal. -/
theorem selectorOverhead_tendsto (D v : ℕ) :
    Tendsto (fun t : ℕ => (2 * D * (v * Real.logb 2 ((t : ℝ) + 1) + 1)) / t)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun t : ℕ => Real.logb 2 t / t) atTop (𝓝 0) :=
    Real.isLittleO_logb_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun t : ℕ => (t : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hshift := (Real.tendsto_logb_nat_add_one_sub_logb (b := 2)).mul hinv
  have hshifted : Tendsto (fun t : ℕ => Real.logb 2 ((t : ℝ) + 1) / t) atTop (𝓝 0) := by
    convert hshift.add hlog using 1
    · ext t
      ring
    · norm_num
  convert ((hshifted.const_mul (v : ℝ)).add hinv).const_mul (2 * (D : ℝ)) using 1
  · ext t
    ring
  · simp

/-- Inequality (3.1) pays for the data cables and all selector cables at
every sufficiently large tensor power, for any number of terms up to the
polynomial-times-exponential expansion bound. -/
theorem eventually_selector_strict_saving (D m L v : ℕ) (w : ℝ) (hL : 0 < L)
    (hsave : w + 2 * D * Real.logb 2 L < 2 * D * m) :
    ∀ᶠ t : ℕ in atTop, ∀ A ≤ (t + 1) ^ v * L ^ t,
      (t : ℝ) * w + 2 * D * (Nat.clog 2 A : ℝ) < t * (2 * D * m) := by
  have hgap : 0 < 2 * (D : ℝ) * m - (w + 2 * D * Real.logb 2 L) := sub_pos.mpr hsave
  filter_upwards [(selectorOverhead_tendsto D v).eventually_lt_const hgap,
    eventually_gt_atTop (0 : ℕ)] with t hbudget ht
  intro A hA
  have hwidth : (Nat.clog 2 A : ℝ) ≤
      v * Real.logb 2 (t + 1) + t * Real.logb 2 L + 1 := by
    apply le_trans _ (selectorWidth_le t v L hL)
    exact_mod_cast Nat.clog_mono_right 2 hA
  have hdata := mul_le_mul_of_nonneg_left hwidth (by positivity : 0 ≤ 2 * (D : ℝ))
  have hbudget' := (div_lt_iff₀ (Nat.cast_pos.mpr ht : 0 < (t : ℝ))).mp hbudget
  linarith only [hdata, hbudget']

end Crossing

end BorderVNP
end Computability
end OAI
