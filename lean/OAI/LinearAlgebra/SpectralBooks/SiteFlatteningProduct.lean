import OAI.LinearAlgebra.SpectralBooks.SiteFlattening
import OAI.LinearAlgebra.SpectralBooks.KroneckerRank

/-! # Multiplicativity of matrix rank across a cut of tensor sites -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Classical Kronecker
noncomputable section

namespace SiteTensor

open Crossing

variable {I K : Type*} (s : I → Prop) [DecidablePred s]
  {A B : I → Type*}

/-- Flattening a sitewise tensor product pairs the row coordinates of its two
factors, and likewise pairs their column coordinates. -/
theorem cutMatrix_product [Mul K] (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    cutMatrix s (fun z : ∀ i, A i × B i ↦ T (fun i ↦ (z i).1) * U (fun i ↦ (z i).2)) =
      ((cutMatrix s T) ⊗ₖ (cutMatrix s U)).submatrix
        (Equiv.arrowProdEquivProdArrow {i // s i} (fun i ↦ A i.val) (fun i ↦ B i.val))
        (Equiv.arrowProdEquivProdArrow {i // ¬s i} (fun i ↦ A i.val) (fun i ↦ B i.val)) := by
  ext r c
  change T _ * U _ = T _ * U _
  apply congrArg₂ (· * ·)
  · apply congrArg T
    funext i
    by_cases h : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, h,
      Equiv.arrowProdEquivProdArrow]
  · apply congrArg U
    funext i
    by_cases h : s i <;> simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, h,
      Equiv.arrowProdEquivProdArrow]

/-- The flattening rank across any fixed cut is multiplicative under sitewise
tensor product. -/
theorem cutMatrix_rank_product [Field K] [Fintype I] [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (T : (∀ i, A i) → K) (U : (∀ i, B i) → K) :
    (cutMatrix s (fun z : ∀ i, A i × B i ↦ T (fun i ↦ (z i).1) * U (fun i ↦ (z i).2))).rank =
      (cutMatrix s T).rank * (cutMatrix s U).rank := by
  rw [cutMatrix_product, Matrix.rank_submatrix, rank_kronecker]

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
