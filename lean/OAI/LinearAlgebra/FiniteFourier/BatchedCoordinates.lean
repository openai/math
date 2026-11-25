import OAI.LinearAlgebra.FiniteFourier.Batched
import OAI.LinearAlgebra.FiniteFourier.BatchedListBlocks
import OAI.LinearAlgebra.FiniteFourier.BatchedListSpecialization
import OAI.LinearAlgebra.FiniteFourier.InverseComplexity
import OAI.LinearAlgebra.FiniteFourier.GroupReindex
import OAI.LinearAlgebra.FiniteFourier.CharacterExtension

/-! # Symmetric coordinates for the transposed input-output list -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical Matrix NNReal
noncomputable section

universe u v w
variable {K : Type v} {F : Type w} [Field K] [Field F] {n : ℕ}

theorem block_matrix_as_table (B : FourierBlock.{u,v} K n) :
    ∃ (s : K) (row : Fin n ≃ Character B.G K) (col : Fin n ≃ B.G),
      s ≠ 0 ∧ B.matrix = s • (fourierMatrix B.G K).submatrix row col := by
  unfold FourierBlock.matrix
  split
  · obtain ⟨r, c, he⟩ := exists_reindex_inverseFourierMatrix B.G K B.admissible
    rw [he]
    exact ⟨_, B.points.trans r.symm, B.frequencies.trans c.symm, inv_ne_zero B.admissible.1, rfl⟩
  · exact ⟨1, B.frequencies, B.points, one_ne_zero, (one_smul _ _).symm⟩

theorem block_symmetric_coordinates (B : FourierBlock.{u,v} K n) (f : K →+* F) :
    ∃ (e : Shrink.{0} B.G ≃ Character (Shrink.{0} B.G) F)
      (r c : Shrink.{0} B.G ≃ Fin n) (s : F),
      s ≠ 0 ∧
      let H := (fourierMatrix (Shrink.{0} B.G) F).submatrix e id
      Hᵀ = H ∧ (B.matrix.map f)ᵀ.submatrix r c = s • H := by
  let g : B.G ≃+ Shrink.{0} B.G := Shrink.addEquiv.symm
  let h := (B.admissible.map f).of_groupEquiv g
  obtain ⟨self, hself⟩ := exists_symmetric_character_equiv _ _ h
  let e := Multiplicative.ofAdd.trans self.toEquiv
  obtain ⟨s, row, col, hs, he⟩ := block_matrix_as_table B
  let r := g.symm.toEquiv.trans col.symm
  let ext := (characterExtensionEquiv B.admissible f).trans (characterGroupEquiv g)
  let c := e.trans (ext.symm.trans row.symm)
  let H := (fourierMatrix (Shrink.{0} B.G) F).submatrix e id
  have hsymm : Hᵀ = H := by
    ext i j
    exact congrArg Units.val (hself j i)
  refine ⟨e, r, c, f s, by simpa using f.injective.ne hs, hsymm, ?_⟩
  have hforward : (B.matrix.map f).submatrix c r = f s • H := by
    ext i j
    rw [he]
    change f (s * _) = f s * fourierMatrix (Shrink.{0} B.G) F (e i) j
    rw [map_mul]
    congr 1
    rw [← reindex_fourierMatrix (K := F) g]
    change f (fourierMatrix B.G K (row (row.symm (ext.symm (e i)))) (col (col.symm (g.symm j)))) =
      fourierMatrix B.G F ((characterGroupEquiv g).symm (e i)) (g.symm j)
    rw [row.apply_symm_apply, col.apply_symm_apply]
    have hχ : characterExtensionEquiv B.admissible f (ext.symm (e i)) =
        (characterGroupEquiv g).symm (e i) := (characterExtensionEquiv B.admissible f).apply_symm_apply _
    change fourierMatrix B.G F (characterExtensionEquiv B.admissible f (ext.symm (e i))) (g.symm j) = _
    rw [hχ]
  change ((B.matrix.map f).submatrix c r)ᵀ = f s • H
  rw [hforward, Matrix.transpose_smul, hsymm]

variable {R D : Type} [Fintype R] [Fintype D] [DecidableEq R] [DecidableEq D]

theorem listValue_augmented_reindex
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop))
    (M Q : Matrix R R K) (H : Matrix D D K) (r c : D ≃ R) (s : K) (hs : s ≠ 0)
    (he : M.submatrix r c = s • H) :
    listValue φ (Q.submatrix r r * Matrix.fromCols (1 : Matrix D D K) H) ≤
      listValue φ (Q * Matrix.fromCols (1 : Matrix R R K) M) := by
  let e := r.sumCongr c
  let A := (Q * Matrix.fromCols (1 : Matrix R R K) M).submatrix r e
  have ha : A = Q.submatrix r r * Matrix.fromCols (1 : Matrix D D K) (s • H) := by
    unfold A
    rw [Matrix.submatrix_mul _ _ r r e r.bijective, ← he]
    congr 1
    ext i j
    cases j <;> simp [e, Matrix.one_apply]
  let scale := Sum.elim (fun _ : D => (1:K)) (fun _ : D => s⁻¹)
  have hscale : Matrix.of (fun i j => 1 * A i j * scale j) =
      Q.submatrix r r * Matrix.fromCols (1 : Matrix D D K) H := by
    rw [ha, Matrix.mul_fromCols, Matrix.mul_fromCols, Matrix.mul_smul]
    ext i j
    cases j <;> simp [scale, mul_right_comm, hs]
  rw [← hscale]
  exact (listValue_scale_le φ A (fun _ => 1) scale).trans_eq (listValue_reindex φ _ r e)

end
end FiniteFourier
end LinearAlgebra
end OAI
