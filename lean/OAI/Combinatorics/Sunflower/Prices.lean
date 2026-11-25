import OAI.LinearAlgebra.SpectralBooks.MaskDiagonalPrice
import OAI.LinearAlgebra.SpectralBooks.PlacedSpectralWires

/-! # Diagonal prices and the equality-filter cost recurrence -/

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

noncomputable section

variable {I F : Type*} [Fintype I] [Nonempty I] [Field F]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I F → _ → Prop))

/-- Naming the labels by any finite nonempty alphabet preserves the price formula. -/
theorem rawLogPrice_maskDiagonal_card (c : ℝ) (S : Finset I) (hS : S.Nonempty)
    (α : Type) [Fintype α] [Nonempty α] :
    rawLogPrice φ c (Raw.maskDiagonal F S α) =
      maskDiagonalPrice φ c S * Real.logb 2 (Fintype.card α) := by
  classical
  have he := ofRaw_maskDiagonal_equiv (K := F) S hS (Fintype.equivFin α)
  calc
    _ = rawLogPrice φ c (Raw.maskDiagonal F S (Fin (Fintype.card α))) :=
      congrArg (fun z ↦ c * Real.logb 2 (φ.val z : ℝ)) he
    _ = _ := rawLogPrice_maskDiagonal φ c S hS Fintype.card_pos

/-- The value before taking logarithms, for an arbitrary finite alphabet. -/
theorem spectralValue_maskDiagonal_card (S : Finset I) (hS : S.Nonempty)
    (α : Type) [Fintype α] [Nonempty α] :
    (φ.val (ofRaw (Raw.maskDiagonal F S α)) : ℝ) =
      (Fintype.card α : ℝ) ^ maskDiagonalPrice φ 1 S := by
  classical
  have hp : 0 < (φ.val (ofRaw (Raw.maskDiagonal F S α)) : ℝ) := by
    exact_mod_cast zero_lt_one.trans_le
      (one_le_raw_spectralValue φ _ (Raw.maskDiagonal_ne_zero S hS α))
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (Real.strictMonoOn_logb (by norm_num : (1 : ℝ) < 2)).injOn hp
    (Real.rpow_pos_of_pos hc _)
  rw [Real.logb_rpow_eq_mul_logb_of_pos hc]
  simpa only [rawLogPrice, one_mul] using rawLogPrice_maskDiagonal_card φ 1 S hS α

/-- The full support costs one unit per shared bit at every normalized point. -/
@[simp] theorem maskDiagonalPrice_univ (c : ℝ) :
    maskDiagonalPrice φ c (Finset.univ : Finset I) = c := by
  have hv := map_natCast (normalizedSpectrum.toRingHom φ) 2
  change φ.val (2 : TensorClass.{0} I F) = 2 at hv
  simp [maskDiagonalPrice, rawLogPrice, ofRaw_maskDiagonal_univ, hv]

theorem maskDiagonalPrice_le_one (S : Finset I) : maskDiagonalPrice φ 1 S ≤ 1 := by
  classical
  simpa only [maskDiagonalPrice_univ] using
    maskDiagonalPrice_mono φ (zero_le_one : (0 : ℝ) ≤ 1) (Finset.subset_univ S)

/-- Value of a raw tensor as a real number. -/
abbrev spectralValue (X : Raw.{0} I F) : ℝ := (φ.val (ofRaw X) : ℝ)

theorem spectralValue_pos {X : Raw.{0} I F} (h : X.coeff ≠ 0) : 0 < spectralValue φ X := by
  exact_mod_cast zero_lt_one.trans_le (one_le_raw_spectralValue φ X h)

@[simp] theorem spectralValue_mul (X Y : Raw.{0} I F) :
    spectralValue φ (X.mul Y) = spectralValue φ X * spectralValue φ Y := by
  simp only [spectralValue, ofRaw_mul, φ.property.2.2.2.1, NNReal.coe_mul]

@[simp] theorem spectralValue_add (X Y : Raw.{0} I F) :
    spectralValue φ (X.add Y) = spectralValue φ X + spectralValue φ Y := by
  simp only [spectralValue, ofRaw_add, φ.property.2.2.1, NNReal.coe_add]

theorem logb_spectralValue_div {U V : Raw.{0} I F} (hU : U.coeff ≠ 0)
    (hV : V.coeff ≠ 0) :
    Real.logb 2 (spectralValue φ U / spectralValue φ V) =
      rawLogPrice φ 1 U - rawLogPrice φ 1 V := by
  rw [Real.logb_div (spectralValue_pos φ hU).ne' (spectralValue_pos φ hV).ne']
  simp only [rawLogPrice, spectralValue, one_mul]

/-- A correction of known logarithmic cost, discounted by the matching labels. -/
theorem spectralRatio_div_maskDiagonal_le {U V : Raw.{0} I F} (hU : U.coeff ≠ 0)
    (hV : V.coeff ≠ 0) (S : Finset I) (hS : S.Nonempty)
    (α : Type) [Fintype α] [Nonempty α] {c : ℝ}
    (hc : rawLogPrice φ 1 U - rawLogPrice φ 1 V ≤ c) :
    spectralValue φ U / (spectralValue φ V * spectralValue φ (Raw.maskDiagonal F S α)) ≤
      (2 : ℝ) ^ (c - maskDiagonalPrice φ 1 S * Real.logb 2 (Fintype.card α)) := by
  classical
  have hD := spectralValue_pos φ (Raw.maskDiagonal_ne_zero (K := F) S hS α)
  rw [← div_div]
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (div_pos (div_pos (spectralValue_pos φ hU) (spectralValue_pos φ hV)) hD)).mp
  rw [Real.logb_div (div_pos (spectralValue_pos φ hU) (spectralValue_pos φ hV)).ne' hD.ne',
    logb_spectralValue_div φ hU hV]
  have hprice := rawLogPrice_maskDiagonal_card φ 1 S hS α
  simp only [rawLogPrice, one_mul] at hprice
  rw [show Real.logb 2 (spectralValue φ (Raw.maskDiagonal F S α)) = _ from hprice]
  exact sub_le_sub_right hc _

/-- The exact ratio recurrence for one equality-filter step, with `D` the
diagonal bearing the nonzero matching index. The direct sum is taken on the
whole set of sites, so the denominator retains the ambient price of `D`. -/
theorem spectralRatio_filter_step (R Q U V D : Raw.{0} I F)
    (hQ : Q.coeff ≠ 0) (hV : V.coeff ≠ 0) (hD : D.coeff ≠ 0) :
    spectralValue φ ((R.mul (V.mul D)).add (Q.mul U)) /
        spectralValue φ (Q.mul (V.mul D)) =
      spectralValue φ R / spectralValue φ Q +
        spectralValue φ U / (spectralValue φ V * spectralValue φ D) := by
  simp only [spectralValue_add, spectralValue_mul]
  field_simp [(spectralValue_pos φ hQ).ne', (spectralValue_pos φ hV).ne',
    (spectralValue_pos φ hD).ne']

end
end Sunflower
end Combinatorics
end OAI
