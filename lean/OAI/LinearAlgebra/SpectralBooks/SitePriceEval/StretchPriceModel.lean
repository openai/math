import OAI.LinearAlgebra.SpectralBooks.BookRaw
import OAI.LinearAlgebra.SpectralBooks.RawLogPrice
import OAI.LinearAlgebra.SpectralBooks.SitePriceEval.StretchWordPrice
import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary

/-!
# Spectral prices on the common site and its two private site families
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators Classical NNReal

namespace SitePriceEval

open SiteTensor

variable {K : Type*} [Field K] {B C : Type} [Fintype B] [Fintype C]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (BookSite B C) K → _ → _))

/-- Evaluate the scaled log of a normalized point on each individual-site tensor. -/
def ofSpectralPoint (c : ℝ) (hc : 0 ≤ c) : SitePriceEval K B C where
  value T := rawLogPrice φ c (bookRaw T)
  mono h := rawLogPrice_mono φ hc ((bookRaw_restricts_iff _ _).mpr h)

variable {U V : Type} {X X' : B → Type} {Y Y' : C → Type}
  [Fintype U] [Fintype V] [∀ b, Fintype (X b)] [∀ b, Fintype (X' b)]
  [∀ c, Fintype (Y c)] [∀ c, Fintype (Y' c)]

/-- Product coordinates at the common and private sites describe the raw tensor
product after reindexing the basis separately at each site. -/
theorem bookRaw_splitProduct
    (T : Tensor K U (∀ b, X b) (∀ c, Y c)) (S : Tensor K V (∀ b, X' b) (∀ c, Y' c)) :
    ofRaw (bookRaw (splitProduct T S)) = ofRaw ((bookRaw T).mul (bookRaw S)) := by
  apply ofRaw_eq_iff.mpr
  let e : ∀ i, (bookRaw (splitProduct T S)).Leg i ≃ ((bookRaw T).mul (bookRaw S)).Leg i
    | .inl _ => Equiv.refl _
    | .inr (.inl _) => Equiv.refl _
    | .inr (.inr _) => Equiv.refl _
  exact Raw.reindex_equivalent e (fun _ => rfl)

/-- A normalized point's logarithmic price adds on nonzero book products. -/
theorem ofSpectralPoint_binaryProductAdditive (c : ℝ) (hc : 0 ≤ c) :
    (ofSpectralPoint φ c hc).BinaryProductAdditive := by
  intro U V X X' Y Y' _ _ _ _ _ _ T S hT hS
  change rawLogPrice φ c (bookRaw (splitProduct T S)) = _
  calc
    _ = rawLogPrice φ c ((bookRaw T).mul (bookRaw S)) :=
      congrArg (fun x => c * Real.logb 2 (φ.val x : ℝ)) (bookRaw_splitProduct T S)
    _ = _ := rawLogPrice_mul φ c _ _ ((bookRaw_coeff_ne_zero_iff _).mpr hT)
      ((bookRaw_coeff_ne_zero_iff _).mpr hS)

/-- In particular the price of a product word is the sum of the letter prices. -/
theorem ofSpectralPoint_wordProductAdditive (c : ℝ) (hc : 0 ≤ c) :
    (ofSpectralPoint φ c hc).WordProductAdditive :=
  wordProductAdditive_of_binaryProductAdditive _ (ofSpectralPoint_binaryProductAdditive φ c hc)

/-- The finite ordinary-sum estimate extends to a zero total or zero summands. -/
theorem ofSpectralPoint_ordinarySumBound (c : ℝ) (hc : 0 ≤ c) :
    (ofSpectralPoint φ c hc).OrdinarySumBound c := by
  intro L U X Y _ _ _ _ _ T
  let S : Tensor K U (∀ b, X b) (∀ i, Y i) := fun u x y => ∑ l, T l u x y
  let t : L → (∀ i, bookLeg U X Y i) → K := fun l => (bookRaw (T l)).coeff
  have he : (bookRaw S).coeff = ∑ l, t l := by
    funext a
    change (∑ l, t l a) = (∑ l, t l) a
    exact (Finset.sum_apply a Finset.univ t).symm
  change ∃ i, rawLogPrice φ c (bookRaw S) ≤ rawLogPrice φ c (bookRaw (T i)) + _
  by_cases hS : (bookRaw S).coeff = 0
  · refine ⟨Classical.arbitrary L, ?_⟩
    rw [rawLogPrice_zero φ c _ hS]
    apply add_nonneg (rawLogPrice_nonneg φ hc _) (mul_nonneg hc _)
    apply Real.logb_nonneg (by norm_num)
    exact_mod_cast Nat.succ_le_of_lt Fintype.card_pos
  · have ht : ∑ l, t l ≠ 0 := he ▸ hS
    obtain ⟨i, _, hi⟩ := ordinary_sum_logb_le φ t ht hc
    refine ⟨i, ?_⟩
    change c * Real.logb 2 (coeffValue φ (bookRaw S).coeff) ≤ _
    rw [he]
    exact hi

/-- On a submonoid of tensor classes dominating the scalar unit, this coordinate
evaluation agrees with the scaled additive price of the same class. -/
theorem ofSpectralPoint_agrees (c : ℝ) (hc : 0 ≤ c)
    {P : Submonoid (TensorClass.{0} (BookSite B C) K)} (hu : ∀ t : P, 1 ≤ t.val)
    (T : Tensor K U (∀ b, X b) (∀ i, Y i)) (hT : ofRaw (bookRaw T) ∈ P) :
    (ofSpectralPoint φ c hc).value T =
      (c • spectralLogHom hu φ) (Additive.ofMul (⟨ofRaw (bookRaw T), hT⟩ : P)) := rfl

end SitePriceEval

end

end SpectralBooks
end LinearAlgebra
end OAI
