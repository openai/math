import OAI.LinearAlgebra.SpectralBooks.SitePriceEval.StretchPriceModel
import OAI.LinearAlgebra.SpectralBooks.SubsetPriceOrdinary

/-!
# Prices in the presence of auxiliary sites

The point lives on the full ambient tensor semiring. Book tensors have scalar
coordinates at the auxiliary sites. Their ordinary-sum coefficient is the
price of the binary diagonal on the occupied sites.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators Classical NNReal

section

open SiteTensor

/-- Adding scalar slots preserves nonvanishing of the coefficient tensor. -/
theorem SiteTensor.Raw.withTrivial_coeff_ne_zero_iff {I K : Type*} [Zero K] (O : Type*)
    (T : Raw I K) : (Raw.withTrivial O T).coeff ≠ 0 ↔ T.coeff ≠ 0 := by
  apply not_congr
  constructor
  · intro h
    funext x
    exact congrFun h ((Raw.withTrivialIndex O T).symm x)
  · intro h
    funext x
    exact congrFun h ((Raw.withTrivialIndex O T) x)

namespace SitePriceEval

variable {K : Type*} [Field K] {B C O : Type} [Fintype B] [Fintype C] [Fintype O]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (BookSite B C ⊕ O) K → _ → _))

/-- Coordinate evaluation of an ambient price on tensors supported on the book sites. -/
def ofSupportedSpectralPoint (c : ℝ) (hc : 0 ≤ c) : SitePriceEval K B C where
  value T := rawLogPrice φ c (Raw.withTrivial O (bookRaw T))
  mono h := rawLogPrice_mono φ hc (Raw.withTrivial_restricts O ((bookRaw_restricts_iff _ _).mpr h))

/-- The tensor product is computed in the entire ambient site set. -/
theorem ofSupportedSpectralPoint_binaryProductAdditive (c : ℝ) (hc : 0 ≤ c) :
    (ofSupportedSpectralPoint φ c hc).BinaryProductAdditive := by
  intro U V X X' Y Y' _ _ _ _ _ _ T S hT hS
  have he := congrArg (withTrivialHom O) (bookRaw_splitProduct T S)
  have hl := ofRaw_eq_iff.mpr (Raw.withTrivial_mul_equivalent O (bookRaw T) (bookRaw S))
  change rawLogPrice φ c (Raw.withTrivial O (bookRaw (splitProduct T S))) = _
  calc
    _ = rawLogPrice φ c ((Raw.withTrivial O (bookRaw T)).mul (Raw.withTrivial O (bookRaw S))) :=
      congrArg (fun x => c * Real.logb 2 (φ.val x : ℝ)) (he.trans hl)
    _ = _ := rawLogPrice_mul φ c _ _
      ((Raw.withTrivial_coeff_ne_zero_iff O _).mpr ((bookRaw_coeff_ne_zero_iff _).mpr hT))
      ((Raw.withTrivial_coeff_ne_zero_iff O _).mpr ((bookRaw_coeff_ne_zero_iff _).mpr hS))

/-- Additivity on arbitrary products of letters with one-dimensional outside slots. -/
theorem ofSupportedSpectralPoint_wordProductAdditive (c : ℝ) (hc : 0 ≤ c) :
    (ofSupportedSpectralPoint φ c hc).WordProductAdditive :=
  wordProductAdditive_of_binaryProductAdditive _ (ofSupportedSpectralPoint_binaryProductAdditive φ c hc)

/-- Ordinary sums of tensors supported on the book use the supported binary
diagonal as their logarithmic coefficient. -/
theorem ofSupportedSpectralPoint_ordinarySumBound (c : ℝ) (hc : 0 ≤ c) :
    (ofSupportedSpectralPoint φ c hc).OrdinarySumBound
      (rawLogPrice φ c (Raw.supportDiagonal (BookSite B C) O K (Fin 2))) := by
  intro L U X Y _ _ _ _ _ T
  let S : Tensor K U (∀ b, X b) (∀ i, Y i) := fun u x y => ∑ l, T l u x y
  let t : L → (∀ i, bookLeg U X Y i) → K := fun l => (bookRaw (T l)).coeff
  have he : (bookRaw S).coeff = ∑ l, t l := by
    funext a
    exact (Finset.sum_apply a Finset.univ t).symm
  change ∃ i, rawLogPrice φ c (Raw.withTrivial O (bookRaw S)) ≤
    rawLogPrice φ c (Raw.withTrivial O (bookRaw (T i))) + _
  by_cases hS : (bookRaw S).coeff = 0
  · refine ⟨Classical.arbitrary L, ?_⟩
    have hz : (Raw.withTrivial O (bookRaw S)).coeff = 0 :=
      not_iff_not.mp (Raw.withTrivial_coeff_ne_zero_iff O _) |>.mpr hS
    rw [rawLogPrice_zero φ c _ hz]
    apply add_nonneg (rawLogPrice_nonneg φ hc _) (mul_nonneg (rawLogPrice_nonneg φ hc _) _)
    apply Real.logb_nonneg (by norm_num)
    exact_mod_cast Nat.succ_le_of_lt Fintype.card_pos
  · have ht : ∑ l, t l ≠ 0 := he ▸ hS
    obtain ⟨i, _, hi⟩ := subset_ordinary_sum_logb_le φ t ht hc
    refine ⟨i, ?_⟩
    change c * Real.logb 2 (φ.val (withTrivialHom O (ofCoeffs (bookRaw S).coeff)) : ℝ) ≤ _
    rw [he]
    exact hi

end SitePriceEval
end

end

end SpectralBooks
end LinearAlgebra
end OAI
