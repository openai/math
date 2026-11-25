import OAI.Computability.NearSquareRoot.SynchronizedBoxLayout

/-! # Unitarity of every global layer

This gives the norm-one gain needed for finite-precision error propagation
at every layer boundary of a synchronized short transform.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedPair SynchronizedPadding

private theorem unitary_submatrix {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (M : Matrix X X ℂ) (h : Mᴴ * M = 1) (e : Y ≃ X) :
    (M.submatrix e e)ᴴ * M.submatrix e e = 1 := by
  rw [conjTranspose_submatrix, submatrix_mul_equiv, h, submatrix_one_equiv]

private theorem unitary_permutation {X : Type} [Fintype X] [DecidableEq X] (e : Equiv.Perm X) :
    ((e.toPEquiv.toMatrix : Matrix X X ℂ)ᴴ) * e.toPEquiv.toMatrix = 1 := by
  have h : ((e.toPEquiv.toMatrix : Matrix X X ℂ)ᴴ) = e.symm.toPEquiv.toMatrix := by
    ext i j
    simp only [conjTranspose_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_some_iff, Equiv.symm_apply_eq]
    by_cases hi : e j = i
    · simp [hi]
    · simp [hi, Ne.symm hi]
  rw [h, PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp [one_apply, PEquiv.toMatrix_apply]

private theorem walsh_self_adjoint : walshᴴ = walsh := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [walsh, conjTranspose_apply]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A S : ι → Type}
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- Every exact global layer is unitary, including a Walsh slot with no active blocks. -/
theorem GlobalStage.unitary {bits : ∀ i, A i ≃ Fin 2 × S i}
    {M : Matrix (∀ i, A i) (∀ i, A i) ℂ} (hM : GlobalStage bits M) : Mᴴ * M = 1 := by
  classical
  cases hM with
  | permutation p => exact unitary_permutation _
  | diagonal d h =>
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    change Matrix.diagonal _ = Matrix.diagonal _
    congr 1
    funext x
    change star (∏ i, d i (x i)) * (∏ i, d i (x i)) = 1
    rw [Complex.star_def, Complex.conj_mul', norm_prod]
    simp [h]
  | walsh active =>
    have hu (i : ι) : (SynchronizedSelected.block active bits i)ᴴ *
        SynchronizedSelected.block active bits i = 1 := by
      by_cases hi : i ∈ active
      · have h : SynchronizedSelected.block active bits i =
            (blockDiagonal (fun _ : S i => SynchronizedPair.walsh)).submatrix (bits i) (bits i) := by
          ext x y
          simp [SynchronizedSelected.block, hi, blockDiagonal_apply]
        rw [h]
        apply unitary_submatrix
        rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul]
        simp_rw [walsh_self_adjoint, walsh_sq]
        exact blockDiagonal_one
      · simp [SynchronizedSelected.block, hi]
    rw [tensorMatrix_conjTranspose, ← tensorMatrix_mul]
    simp_rw [hu]
    exact tensorMatrix_one

/-- Reading the same stage in flat physical address order preserves its unitarity. -/
theorem BoxStage.unitary {d : ℕ} {A : Fin d → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    {T : Fin (d/4) → Type} [∀ j, Fintype (T j)] [∀ j, DecidableEq (T j)]
    {hd : 4 ≤ d} {bits : ∀ j, SynchronizedBlocks.BlockAddress A j ≃ Fin 2 × T j}
    {M : Matrix (∀ i, A i) (∀ i, A i) ℂ} (hM : BoxStage hd bits M) : Mᴴ * M = 1 := by
  obtain ⟨N, hn, rfl⟩ := hM
  exact unitary_submatrix N hn.unitary _

end ShortFourier

end NearSquareRoot
end Computability
end OAI
