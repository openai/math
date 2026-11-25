import OAI.LinearAlgebra.SpectralBooks.PriceSelection
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Nonzero

/-!
# Scaled logarithmic prices on finite-site tensor classes

A nonzero field tensor restricts to the scalar unit, so every normalized point takes
values in `{0} ∪ [1,∞)`. Lean's convention `log 0 = 0` therefore extends a log
price monotonically to the zero tensor.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open scoped NNReal

namespace SiteTensor

universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → _))

/-- The price of a raw tensor at a normalized spectral point and a common scale. -/
def rawLogPrice (c : ℝ) (X : Raw.{v} I K) : ℝ :=
  c * Real.logb 2 (φ.val (ofRaw X) : ℝ)

/-- The positivity needed when taking the logarithm of a nonzero tensor. -/
theorem one_le_raw_spectralValue (X : Raw.{v} I K) (h : X.coeff ≠ 0) :
    1 ≤ φ.val (ofRaw X) :=
  one_le_spectral_value φ (X.one_restricts_of_nonzero h)

/-- The zero tensor has price zero. -/
theorem rawLogPrice_zero (c : ℝ) (X : Raw.{v} I K) (h : X.coeff = 0) :
    rawLogPrice φ c X = 0 := by
  simp [rawLogPrice, (ofRaw_eq_zero_iff X).mpr h, φ.property.1]

/-- At a nonnegative scale every tensor has nonnegative price. -/
theorem rawLogPrice_nonneg {c : ℝ} (hc : 0 ≤ c) (X : Raw.{v} I K) :
    0 ≤ rawLogPrice φ c X := by
  by_cases h : X.coeff = 0
  · rw [rawLogPrice_zero φ c X h]
  · apply mul_nonneg hc (Real.logb_nonneg (by norm_num) _)
    exact_mod_cast one_le_raw_spectralValue φ X h

/-- Scaled log price respects the actual local-matrix restriction preorder,
including when a restriction annihilates the input. -/
theorem rawLogPrice_mono {c : ℝ} (hc : 0 ≤ c) {X Y : Raw.{v} I K}
    (h : X.Restricts Y) : rawLogPrice φ c X ≤ rawLogPrice φ c Y := by
  by_cases hX : X.coeff = 0
  · rw [rawLogPrice_zero φ c X hX]
    exact rawLogPrice_nonneg φ hc _
  · apply mul_le_mul_of_nonneg_left _ hc
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue φ X hX)
    · exact_mod_cast φ.property.2.2.2.2 (ofRaw X) (ofRaw Y) h

/-- Multiplicativity of a normalized point gives additivity of price on nonzero
tensor factors. -/
theorem rawLogPrice_mul (c : ℝ) (X Y : Raw.{v} I K)
    (hX : X.coeff ≠ 0) (hY : Y.coeff ≠ 0) :
    rawLogPrice φ c (X.mul Y) = rawLogPrice φ c X + rawLogPrice φ c Y := by
  have pos (T : Raw.{v} I K) (h : T.coeff ≠ 0) : (φ.val (ofRaw T) : ℝ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans_le (one_le_raw_spectralValue φ T h)).ne'
  simp only [rawLogPrice, ofRaw_mul, φ.property.2.2.2.1, NNReal.coe_mul,
    Real.logb_mul (pos X hX) (pos Y hY), mul_add]

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
