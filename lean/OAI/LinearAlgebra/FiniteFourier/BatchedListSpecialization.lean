import OAI.LinearAlgebra.FiniteFourier.BatchedListTensor
import OAI.LinearAlgebra.FiniteFourier.BatchedDiagonalLimit

/-! # The spectral value of the diagonal blocks of an echelon quotient -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical BigOperators NNReal

variable {K : Type*} [Field K] {R C : Type} [Fintype R] [Fintype C]

private theorem scale_tensor {I : Type} [Fintype I] {A : I → Type} [∀ i, Fintype (A i)]
    (T : (∀ i, A i) → K) (w : ∀ i, A i → K) :
    Crossing.IsRestriction (fun x => T x * ∏ i, w i (x i)) T := by
  refine ⟨fun i x y => if x = y then w i x else 0, fun x => ?_⟩
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    have diff : ∃ i, x i ≠ y i := by
      by_contra! h
      exact hy (funext h).symm
    obtain ⟨i, hi⟩ := diff
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
  · simp

/-- Multiplying each row and each column by its own scalar acts on separate
tensor legs. This is valid even when some scalars are zero. -/
theorem listValue_scale_le
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop))
    (A : Matrix R C K) (r : R → K) (c : C → K) :
    listValue φ (Matrix.of (fun i j => r i * A i j * c j)) ≤ listValue φ A := by
  let w : ∀ i, listLeg R C i → K :=
    Fin.cases r (Fin.cases c (Fin.cases (fun _ => 1) (fun i => i.elim0)))
  apply φ.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr ?_)
  change Crossing.IsRestriction (listRaw (Matrix.of (fun i j => r i * A i j * c j))).coeff
    (listRaw A).coeff
  have h := scale_tensor (A := listLeg R C) (listRaw A).coeff w
  have hc : (listRaw (Matrix.of (fun i j => r i * A i j * c j))).coeff =
      (fun x : ∀ i, listLeg R C i => (listRaw A).coeff x * ∏ i, w i (x i)) := by
    funext x
    rw [Fin.prod_univ_three]
    change (if (x 1 : C) = x 2 then r (x 0) * A (x 0) (x 1) * c (x 1) else 0) =
      (if (x 1 : C) = x 2 then A (x 0) (x 1) else 0) * (r (x 0) * c (x 1) * 1)
    split_ifs <;> ring
  rw [hc]
  exact h

/-- Passing from an upper block triangular list to its block diagonal cannot
increase its spectral value. Row and column blocks may have different sizes. -/
theorem listValue_diagonalBlocks_le [Infinite K]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop))
    (A : Matrix R C K) (row : R → ℕ) (col : C → ℕ)
    (upper : ∀ i j, col j < row i → A i j = 0) :
    listValue φ (Matrix.of (fun i j => if row i = col j then A i j else 0)) ≤ listValue φ A := by
  let scaled (z : K) := Matrix.of (fun i j => (z ^ row i)⁻¹ * A i j * z ^ col j)
  let S := scaled '' {z | z ≠ 0}
  apply listValue_le_of_mem_closure φ (S := S)
  · intro p hp
    exact block_diagonal_specialization A row col upper p fun z hz =>
      hp _ ⟨scaled z, ⟨z, hz, rfl⟩, rfl⟩
  · rintro _ ⟨z, _, rfl⟩
    exact listValue_scale_le φ A _ _

end FiniteFourier
end LinearAlgebra
end OAI
