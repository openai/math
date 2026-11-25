import OAI.LinearAlgebra.SpectralBooks.GroundFieldComparison
import OAI.LinearAlgebra.SpectralBooks.WireClassComparison
import OAI.LinearAlgebra.SpectralBooks.WirePowerClass
import OAI.LinearAlgebra.SpectralBooks.CrossingWireClass

/-! # Shortening the actual crossing from a spectral price gap -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped BigOperators NNReal Classical
noncomputable section

namespace Crossing

open SiteTensor

variable {F : Type*} [Field F]

/-- A semiring inequality with a sum of wires on the right gives ordinary
matrix restriction in the coordinate format used by the network expansion. -/
theorem restrictsWirePower_of_le {I : Type*} [Fintype I] [Nonempty I] {E : Type} [Fintype E]
    (R : Raw.{0} I F) (wires : E → Wire I) (k j : ℕ)
    (h : ofRaw R ≤ k • (∑ e, ofRaw ((wires e).raw F)) ^ j) :
    RestrictsWirePower R.coeff wires k j := by
  rw [← ofRaw_copiesOfWirePower F wires k j] at h
  exact ofRaw_le_iff.mp h

/-- Normalized spectral evaluations on the concrete `2D+1`-site tensor semiring. -/
abbrev AxisSpectrum (F : Type*) [Field F] (D : ℕ) :=
  normalizedSpectrum (S := TensorClass.{0} (AxisSite D) F) (· ≤ ·)

/-- The log price of a binary identity wire at the indicated pair of sites. -/
def pairLogPrice {D : ℕ} (e : AxisPair D) (φ : AxisSpectrum F D) : ℝ :=
  Real.logb 2 (φ.val (ofRaw ((axisWire e 1).raw F)) : ℝ)

/-- The log price of the crossing with one bit on every diameter. -/
def crossingLogPrice {D : ℕ} (φ : AxisSpectrum F D) : ℝ :=
  Real.logb 2 (φ.val (ofRaw (crossingRaw F D 1)) : ℝ)

/-- Strict comparison on the normalized spectrum supplies the concrete copy/power
restriction once the integral widths give a price gap. -/
theorem wirePower_restriction_of_log_cover {D : ℕ} [Nonempty (AxisPair D)]
    (m : ℕ) (b : AxisPair D → ℕ)
    (hcover : ∀ φ : AxisSpectrum F D, ∃ e, (m : ℝ) * crossingLogPrice φ < b e * pairLogPrice e φ) :
    ∃ k : ℕ, 0 < k ∧ ∀ j : ℕ, 0 < j →
      RestrictsWirePower (crossingTensor F D (m * j)) (fun e => axisWire e (b e)) k j := by
  have hn : ofRaw (crossingRaw F D 1) ≠ 0 :=
    fun h => crossingRaw_coeff_ne_zero F D 1 ((ofRaw_eq_zero_iff _).mp h)
  have hw (e : AxisPair D) : ofRaw ((axisWire e 1).raw F) ≠ 0 :=
    fun h => Wire.raw_coeff_ne_zero F _ ((ofRaw_eq_zero_iff _).mp h)
  obtain ⟨k, hk, h⟩ := strict_comparison_of_log_power_cover
    (strictSpectralComparison (AxisSite D) F) _ hn hw m b hcover
  refine ⟨k, hk, fun j hj => restrictsWirePower_of_le (crossingRaw F D (m * j)) _ k j ?_⟩
  have he (e : AxisPair D) : ofRaw ((axisWire e (b e)).raw F) =
      ofRaw ((axisWire e 1).raw F) ^ b e := Wire.ofRaw_setWidth_eq_pow F (axisWire e 1) _
  simpa only [ofRaw_crossingRaw_mul_width, ofRaw_crossingRaw_eq_pow F D m, he] using h j hj

/-- The shortening half of the missing-flat construction needs only strict
spectral comparison and the stated geometric gap at every normalized point. -/
theorem exists_shortenedCrossing_of_spectral_gap {D : ℕ} (hD : 2 ≤ D)
    (gap : ∀ φ : AxisSpectrum F D, ∃ e, crossingLogPrice φ < (2 * D / axisLength e) * pairLogPrice e φ) :
    ∃ n : ℕ, 0 < n ∧ ShortenedCrossing F D n := by
  let _ : CompactSpace (AxisSpectrum F D) := isCompact_iff_compactSpace.mp isCompact_spectrum
  let i : Fin D := ⟨0, by omega⟩
  have : Nonempty (AxisPair D) := ⟨⟨Sym2.mk none (some (i, true)), by simp⟩⟩
  apply exists_shortenedCrossing hD pairLogPrice crossingLogPrice _ _ _ gap
  · exact fun m _ b _ => wirePower_restriction_of_log_cover m b
  · exact fun e => continuous_log_price (ofRaw_one_le_of_nonzero _ (Wire.raw_coeff_ne_zero F _))
  · exact continuous_log_price (ofRaw_one_le_of_nonzero _ (crossingRaw_coeff_ne_zero F D 1))
  · intro e φ
    apply Real.logb_nonneg (by norm_num)
    exact_mod_cast one_le_raw_spectralValue φ _ (Wire.raw_coeff_ne_zero F _)

end Crossing

end

end SpectralBooks
end LinearAlgebra
end OAI
