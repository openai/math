import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Raw
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Matrix flattenings of finite-party coefficient tensors -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

open scoped BigOperators Classical

namespace Crossing

variable {I : Type*} (s : I → Prop) [DecidablePred s]

/-- Separate the indices across the two sides of a cut. -/
abbrev cutEquiv (B : I → Type*) := Equiv.piEquivPiSubtypeProd s B

private theorem cut_symm_left {D : I → Type*} (u : ∀ i : {i // s i}, D i)
      (v : ∀ i : {i // ¬ s i}, D i) (i : {i // s i}) :
      (cutEquiv s D).symm (u,v) i = u i := by
    simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
private theorem cut_symm_right {D : I → Type*} (u : ∀ i : {i // s i}, D i)
      (v : ∀ i : {i // ¬ s i}, D i) (i : {i // ¬ s i}) :
      (cutEquiv s D).symm (u,v) i = v i := by
    simp [cutEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]

/-- Flattening places the indices from the first side of the cut in the rows
and those from the other side in the columns. -/
def cutMatrix {K : Type*} {B : I → Type*} (T : (∀ i, B i) → K) :
    Matrix (∀ i : {i // s i}, B i) (∀ i : {i // ¬ s i}, B i) K :=
  fun r c ↦ T ((cutEquiv s B).symm (r, c))

variable {K : Type*} [Field K] [Fintype I] {A B : I → Type*}
variable [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

omit [∀ i, Fintype (B i)] in
/-- Local linear maps multiply the flattened matrix on its left and right.
Both multipliers are products of the local entries on their respective sides. -/
theorem cutMatrix_factor_of_restriction (X : (∀ i, B i) → K) (Y : (∀ i, A i) → K)
    (h : IsRestriction X Y) :
    ∃ P Q, cutMatrix s X = P * cutMatrix s Y * Q := by
  classical
  obtain ⟨M, hm⟩ := h
  let P : Matrix (∀ i : {i // s i}, B i) (∀ i : {i // s i}, A i) K :=
    fun r a ↦ ∏ i : {i // s i}, M i.val (r i) (a i)
  let Q : Matrix (∀ i : {i // ¬ s i}, A i) (∀ i : {i // ¬ s i}, B i) K :=
    fun a c ↦ ∏ i : {i // ¬ s i}, M i.val (c i) (a i)
  refine ⟨P, Q, ?_⟩
  ext r c
  rw [cutMatrix, hm, ← Equiv.sum_comp (cutEquiv s A).symm, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← Fintype.prod_subtype_mul_prod_subtype s]
  simp only [cut_symm_left, cut_symm_right, P, Q, cutMatrix]
  ring
/-- Matrix rank across any cut decreases under tensor restriction. -/
theorem cutMatrix_rank_le_of_restriction (X : (∀ i, B i) → K) (Y : (∀ i, A i) → K)
    (h : IsRestriction X Y) : (cutMatrix s X).rank ≤ (cutMatrix s Y).rank := by
  obtain ⟨P, Q, e⟩ := cutMatrix_factor_of_restriction s X Y h
  rw [e]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end Crossing

end

end SpectralBooks
end LinearAlgebra
end OAI
