import OAI.LinearAlgebra.FiniteFourier.BatchedListTensor
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Projection

/-! # Rank lost by projecting the vector leg of a list -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped NNReal

variable {K : Type*} [Field K] {R C D : Type} [Fintype R] [Fintype C] [Fintype D]

/-- Extend a right inverse on the image to a matrix on the whole target space. -/
theorem exists_matrix_inner_inverse (Q : Matrix D R K) :
    ∃ E : Matrix R D K, Q * E * Q = Q := by
  classical
  let f := Matrix.toLin' Q
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨p, hp⟩ := Submodule.exists_isCompl (LinearMap.range f)
  let e := g.comp ((LinearMap.range f).projectionOnto p hp)
  refine ⟨LinearMap.toMatrix' e, Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  change (f.comp e).comp f = f
  apply LinearMap.ext
  intro x
  change f (g ((LinearMap.range f).projectionOnto p hp (f x))) = f x
  rw [Submodule.projectionOnto_apply_of_mem_left hp (LinearMap.mem_range_self f x)]
  exact congrArg Subtype.val (LinearMap.congr_fun hg (f.rangeRestrict x))

/-- The unrecovered part of the list fits in the lost rank. Its spectral value
pays for the entire difference between the original and projected list values. -/
theorem exists_low_rank_list_remainder
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop))
    (Q : Matrix D R K) (U : Matrix R C K) :
    ∃ W : Matrix R C K, Q * W = 0 ∧ Q.rank + W.rank ≤ Fintype.card R ∧
      listValue φ U ≤ listValue φ (Q * U) + listValue φ W := by
  obtain ⟨E, hE⟩ := exists_matrix_inner_inverse Q
  let W := U - E * (Q * U)
  have hW : Q * W = 0 := by
    simp only [W, Matrix.mul_sub, ← Matrix.mul_assoc, hE, sub_self]
  refine ⟨W, hW, Matrix.rank_add_rank_le_card_of_mul_eq_zero hW, ?_⟩
  calc
    listValue φ U = listValue φ (E * (Q * U) + W) := by rw [show E * (Q * U) + W = U by dsimp [W]; abel]
    _ ≤ listValue φ (E * (Q * U)) + listValue φ W := listValue_add_le φ _ _
    _ ≤ _ := add_le_add_left (listValue_mul_le φ E (Q * U)) _

end FiniteFourier
end LinearAlgebra
end OAI
