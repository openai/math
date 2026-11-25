import OAI.Computability.NearSquareRoot.SynchronizedStageUnitary

/-! # Adjoint physical stage descriptors -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedPadding SynchronizedPair

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A S : ι → Type}
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

omit [∀ i, Fintype (A i)] [∀ i, Fintype (S i)] in
/-- The reversed stream uses the same three physical slot types. -/
theorem GlobalStage.adjoint {bits : ∀ i, A i ≃ Fin 2 × S i} {M : Matrix (∀ i, A i) (∀ i, A i) ℂ}
    (hm : GlobalStage bits M) : GlobalStage bits Mᴴ := by
  classical
  cases hm with
  | permutation p =>
    have e : (((Equiv.piCongrRight p).toPEquiv.toMatrix : Matrix _ _ ℂ)ᴴ) =
        (Equiv.piCongrRight (fun i => (p i).symm)).toPEquiv.toMatrix := by
      ext x y
      have hi : (Equiv.piCongrRight (fun i => (p i).symm)) x = y ↔
          (Equiv.piCongrRight p) y = x := by
        change (Equiv.piCongrRight p).symm x = y ↔ _
        exact (Equiv.symm_apply_eq _).trans eq_comm
      simp only [conjTranspose_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Option.mem_some_iff, hi]
      split_ifs <;> simp
    rw [e]
    exact .permutation _
  | diagonal d h =>
    have hp : (Matrix.diagonal (fun x : ∀ i, A i => ∏ i, d i (x i)))ᴴ =
        Matrix.diagonal (fun x : ∀ i, A i => ∏ i, star (d i (x i))) := by
      simp [Matrix.diagonal_conjTranspose, star_prod]
    rw [hp]
    exact GlobalStage.diagonal (address := bits) (fun i x => star (d i x)) (fun i x => by simpa using h i x)
  | walsh active =>
    have hw : SynchronizedPair.walshᴴ = SynchronizedPair.walsh := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [SynchronizedPair.walsh, conjTranspose_apply]
    have hblock (i : ι) : (SynchronizedSelected.block active bits i)ᴴ =
        SynchronizedSelected.block active bits i := by
      by_cases hi : i ∈ active
      · have h : SynchronizedSelected.block active bits i =
            (blockDiagonal (fun _ : S i => SynchronizedPair.walsh)).submatrix (bits i) (bits i) := by
          ext x y
          simp [SynchronizedSelected.block, hi, blockDiagonal_apply]
        simp [h, conjTranspose_submatrix, hw]
      · simp [SynchronizedSelected.block, hi]
    rw [tensorMatrix_conjTranspose]
    simp_rw [hblock]
    exact .walsh _

end ShortFourier

end NearSquareRoot
end Computability
end OAI
