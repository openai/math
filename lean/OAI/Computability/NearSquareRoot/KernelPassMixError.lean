import OAI.Computability.IntegerMultiplication.Grid.Faith

/-! # Rounding a common-denominator complex accumulator

A fixed dyadic row can first be accumulated exactly on Gaussian integers. Dropping the
common denominator bits truncates each signed component toward zero, so only one rounding
error per output record occurs, independently of the number of summands.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPassMix

open IntegerMultiplication

/-- Componentwise truncation after dropping denominator bits cannot overflow a record
whose integer width accommodates the magnitude before truncation. -/
theorem divA_fits (d w : ℕ) (z : Grid.Cell)
    (h : ‖Grid.toC z / (2 : ℂ)^d‖ < (2 : ℝ)^w) : Grid.focus w (Grid.divA d z) := by
  have hnorm : ‖Grid.toC z‖ / (2 : ℝ)^d < (2 : ℝ)^w := by
    simpa only [norm_div, norm_pow, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num] using h
  apply Grid.short _ _ hnorm
  exact ⟨(Grid.slash_limit d z.re).trans
      (div_le_div_of_nonneg_right (Grid.into z).1 (by positivity)),
    (Grid.slash_limit d z.im).trans
      (div_le_div_of_nonneg_right (Grid.into z).2 (by positivity))⟩

/-- Re-encoding the two truncated signed components produces precisely the marked output
record read by the next tape pass. -/
theorem spell_rounded (d w : ℕ) (x : Grid.Coef)
    (h : Grid.focus w (Grid.divA d (Grid.content x))) :
    Grid.spell (Grid.fit (Code.tally (w+1), Grid.rest (Code.tally d, x))) =
      Dusk.mark (Grid.wrapMap w (Grid.divA d (Grid.content x))) := by
  rw [Grid.spellG _ (Grid.fit_r _ _), Grid.fit_small, Grid.rest_r]
  rw [Grid.rest_r]
  unfold Grid.focus Grid.tiny at h ⊢
  have hp : (2 : ℤ)^w ≤ 2^(w+1) := pow_le_pow_right₀ (by decide) (Nat.le_succ _)
  exact ⟨lt_of_lt_of_le h.1 hp, lt_of_lt_of_le h.2 hp⟩

/-- Decoding the rounded accumulator differs by at most two grid units. -/
theorem round_error (p d w : ℕ) (z : Grid.Cell)
    (h : ‖Grid.toC z / (2 : ℂ)^d‖ < (2 : ℝ)^w) :
    ‖Grid.meaning p w (Grid.wrapMap w (Grid.divA d z)) -
      Grid.toC z / (2 : ℂ)^d / (2 : ℂ)^p‖ ≤ (2 : ℝ) / 2^p := by
  rw [Grid.meaning, Grid.recovers _ (divA_fits d w z h), ← sub_div, norm_div, norm_pow,
    show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  exact div_le_div_of_nonneg_right (Grid.embedded d z) (by positivity)

/-- The fixed integer accumulator represents the dyadic row evaluated on the actual
encoded inputs before the one final truncation. -/
theorem weighted_value {ι : Type*} [Fintype ι] (p d w : ℕ) (a : ι → ℤ)
    (r : ι → Dusk.Grain w) :
    Grid.toC (∑ i, a i • Grid.aspect (r i)) / (2 : ℂ)^d / (2 : ℂ)^p =
    ∑ i, ((a i : ℂ) / 2^d) * Grid.meaning p w (r i) := by
  simp_rw [Grid.meaning, map_sum, map_zsmul, zsmul_eq_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The sum of absolute coefficients bounds pre-truncation magnitude, and therefore
determines a sufficient integer width for the whole output row. -/
theorem weighted_fits {ι : Type*} [Fintype ι] (p d w : ℕ) (a : ι → ℤ)
    (r : ι → Dusk.Grain w) (B : ℝ) (hr : ∀ i, ‖Grid.meaning p w (r i)‖ ≤ B)
    (headroom : (∑ i, |(a i : ℝ)| / (2 : ℝ)^d) * B * (2 : ℝ)^p < (2 : ℝ)^w) :
    ‖Grid.toC (∑ i, a i • Grid.aspect (r i)) / (2 : ℂ)^d‖ < (2 : ℝ)^w := by
  have h := congrArg norm (weighted_value p d w a r)
  rw [norm_div, norm_pow, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num,
    div_eq_iff (by positivity)] at h
  rw [h]
  apply lt_of_le_of_lt _ headroom
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ i, ‖((a i : ℂ) / (2 : ℂ)^d) * Grid.meaning p w (r i)‖ := norm_sum_le _ _
    _ ≤ _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      simp only [norm_mul, norm_div, norm_pow, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num,
        Complex.norm_intCast]
      gcongr
      exact hr i

theorem weighted_error {ι : Type*} [Fintype ι] (p d w : ℕ) (a : ι → ℤ)
    (r : ι → Dusk.Grain w) (B : ℝ) (hr : ∀ i, ‖Grid.meaning p w (r i)‖ ≤ B)
    (headroom : (∑ i, |(a i : ℝ)| / (2 : ℝ)^d) * B * (2 : ℝ)^p < (2 : ℝ)^w) :
    ‖Grid.meaning p w (Grid.wrapMap w (Grid.divA d (∑ i, a i • Grid.aspect (r i)))) -
      ∑ i, ((a i : ℂ) / 2^d) * Grid.meaning p w (r i)‖ ≤ (2 : ℝ) / 2^p := by
  rw [← weighted_value]
  exact round_error _ _ _ _ (weighted_fits p d w a r B hr headroom)

end KernelPassMix

end NearSquareRoot
end Computability
end OAI
