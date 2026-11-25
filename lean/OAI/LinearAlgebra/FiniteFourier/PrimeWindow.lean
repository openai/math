import OAI.LinearAlgebra.FiniteFourier.PrimePredictor
import OAI.LinearAlgebra.FiniteFourier.PrimeWindowHoeffding
import OAI.LinearAlgebra.FiniteFourier.PrimeWindowSize

/-! # The exceptional shifts in the spectral-repair window

The product of the uniform coordinate laws assigns every full shift the same
weight. Its two-sided Hoeffding estimate therefore bounds the number of
exceptional rows at each frequency.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- Mean of the shifted digit count. -/
def repairWindowMean (ℓ m : ℕ) : ℝ := (m : ℝ) * ((ℓ : ℝ) - 1) / 2

/-- Lower endpoint `⌊μ - B⌋` of the count window. -/
def repairWindowLower (ℓ m : ℕ) : ℤ := ⌊repairWindowMean ℓ m - repairWindowRadius ℓ m⌋

/-- Upper endpoint `⌈μ + B⌉` of the count window. -/
def repairWindowUpper (ℓ m : ℕ) : ℤ := ⌈repairWindowMean ℓ m + repairWindowRadius ℓ m⌉

/-- The degree allowance for interpolation on all integer counts in the window. -/
def repairWindowDegree (ℓ m : ℕ) : ℕ :=
  (repairWindowUpper ℓ m - repairWindowLower ℓ m).toNat

theorem repairWindowLower_add_degree (ℓ m : ℕ) :
    repairWindowLower ℓ m + repairWindowDegree ℓ m = repairWindowUpper ℓ m := by
  have h := Int.floor_le_ceil (repairWindowMean ℓ m)
  simp only [repairWindowDegree, repairWindowLower, repairWindowUpper,
    Int.floor_sub_natCast, Int.ceil_add_natCast]
  omega

theorem repairWindowDegree_le (ℓ m : ℕ) : repairWindowDegree ℓ m ≤ 2 * repairWindowRadius ℓ m + 1 := by
  have h := Int.ceil_le_floor_add_one (repairWindowMean ℓ m)
  simp only [repairWindowDegree, repairWindowLower, repairWindowUpper,
    Int.floor_sub_natCast, Int.ceil_add_natCast]
  omega

/-- Shifts for which the predictor's integer count misses its interpolation interval. -/
def exceptionalShifts {ℓ m : ℕ} [NeZero ℓ] (k : Fin m → ZMod ℓ) : Finset (Fin m → ZMod ℓ) :=
  Finset.univ.filter fun β =>
    (shiftedCount k β : ℤ) ∉ Set.Icc (repairWindowLower ℓ m) (repairWindowUpper ℓ m)

/-- The count predictor returns the common multiplier on every nonexceptional row. -/
theorem eval_countPredictor_of_notMem_exceptionalShifts {K : Type*} [Field K]
    {ℓ m : ℕ} [NeZero ℓ] {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ)
    {k β : Fin m → ZMod ℓ} (hβ : β ∉ exceptionalShifts k) :
    MvPolynomial.eval (queryPowerValues hζ k)
      (countPredictor hζ β (repairWindowLower ℓ m) (repairWindowDegree ℓ m)) =
        ∏ j, digitPhase hζ (k j) := by
  have h : (shiftedCount k β : ℤ) ∈ Set.Icc (repairWindowLower ℓ m) (repairWindowUpper ℓ m) := by
    simpa [exceptionalShifts] using hβ
  apply eval_countPredictor _ _ _ h.1
  simpa only [repairWindowLower_add_degree] using h.2

private theorem uniformShiftMeasure_finset {ℓ m : ℕ} [NeZero ℓ] (s : Finset (Fin m → ZMod ℓ)) :
    (uniformShiftMeasure ℓ m).real (s : Set (Fin m → ZMod ℓ)) =
      (s.card : ℝ) / (ℓ : ℝ) ^ m := by
  rw [uniformShiftMeasure, ← uniformOn_pi, Set.pi_univ, Measure.real,
    uniformOn_univ, Measure.count_apply_finset, ENNReal.toReal_div]
  simp [ZMod.card]

/-- Rounding the endpoints outwards can only decrease the number of exceptional shifts. -/
theorem exceptionalShifts_subset_tail {ℓ m : ℕ} [NeZero ℓ] (k : Fin m → ZMod ℓ) :
    (exceptionalShifts k : Set (Fin m → ZMod ℓ)) ⊆ {β |
      (repairWindowRadius ℓ m : ℝ) ≤
        |(∑ j, ((k j + β j).val : ℝ)) - (m : ℝ) * ((ℓ : ℝ) - 1) / 2|} := by
  intro β hβ
  have hb : (shiftedCount k β : ℤ) < repairWindowLower ℓ m ∨
      repairWindowUpper ℓ m < (shiftedCount k β : ℤ) := by
    have hnot : ¬ (repairWindowLower ℓ m ≤ (shiftedCount k β : ℤ) ∧
        (shiftedCount k β : ℤ) ≤ repairWindowUpper ℓ m) := (Finset.mem_filter.mp hβ).2
    omega
  have hc : (shiftedCount k β : ℝ) = ∑ j, ((k j + β j).val : ℝ) := by
    simp [shiftedCount]
  change (repairWindowRadius ℓ m : ℝ) ≤ |(∑ j, ((k j + β j).val : ℝ)) - repairWindowMean ℓ m|
  rw [← hc, le_abs]
  rcases hb with hl | hr
  · right
    have h₁ : (shiftedCount k β : ℝ) < (repairWindowLower ℓ m : ℝ) := by exact_mod_cast hl
    unfold repairWindowLower at h₁
    linarith [Int.floor_le (repairWindowMean ℓ m - repairWindowRadius ℓ m)]
  · left
    have h₁ : (repairWindowUpper ℓ m : ℝ) < (shiftedCount k β : ℝ) := by exact_mod_cast hr
    unfold repairWindowUpper at h₁
    linarith [Int.le_ceil (repairWindowMean ℓ m + repairWindowRadius ℓ m)]

/-- At every frequency at most `ℓ^m/(2m³)` shifts miss the rounded count window. -/
theorem exceptionalShifts_card_le {ℓ m : ℕ} [NeZero ℓ] (hℓ : 2 ≤ ℓ) (hm : 2 ≤ m)
    (k : Fin m → ZMod ℓ) : (exceptionalShifts k).card ≤ ℓ ^ m / (2 * m ^ 3) := by
  have htail := shiftedCount_tail k (B := (repairWindowRadius ℓ m : ℝ)) (Nat.cast_nonneg _)
  have hprob := (measureReal_mono (μ := uniformShiftMeasure ℓ m)
    (exceptionalShifts_subset_tail k)).trans (htail.trans (repairWindow_exp_le hℓ hm))
  rw [uniformShiftMeasure_finset] at hprob
  have hm₀ : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hℓ₀ : 0 < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hc := (div_le_div_iff₀ (pow_pos hℓ₀ m) (show 0 < 2 * (m : ℝ) ^ 3 by positivity)).mp hprob
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * m ^ 3)).2
  exact_mod_cast (show ((exceptionalShifts k).card : ℝ) * (2 * m ^ 3) ≤ (ℓ : ℝ) ^ m by
    simpa only [one_mul] using hc)

end

end

end FiniteFourier
end LinearAlgebra
end OAI
