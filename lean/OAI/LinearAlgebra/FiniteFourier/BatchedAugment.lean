import OAI.LinearAlgebra.FiniteFourier.BatchedRepetition
import OAI.LinearAlgebra.FiniteFourier.BatchedBlockDetection

/-! # Passing from repeated joint errors to the list of inputs and outputs -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix OAI.LinearAlgebra.SpectralBooks
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] {I R C : Type} [Fintype I] [Fintype R] [Fintype C]

private theorem entryCount_submatrix (A : Matrix I (I ⊕ I) K) (e : R ≃ I) (f : C ≃ I ⊕ I) :
    matrixEntryCount (A.submatrix e f) = matrixEntryCount A := by
  rw [entryCount_sum, entryCount_sum, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro r _
  exact f.sum_comp (fun i => if A (e r) i ≠ 0 then 1 else 0)

variable [DecidableEq I]

private theorem entryCount_augment (A : Matrix I I K) :
    matrixEntryCount (fromCols (1 : Matrix I I K) Aᵀ) = Fintype.card I + matrixEntryCount A := by
  rw [entryCount_sum, entryCount_sum]
  simp_rw [Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr, transpose_apply]
  rw [Finset.sum_add_distrib]
  conv_rhs => rw [Finset.sum_comm]
  congr 1
  have ho (i : I) : (∑ j, if (1 : Matrix I I K) i j ≠ 0 then 1 else 0) = (1 : ℕ) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  exact (Finset.sum_congr rfl (fun i _ => ho i)).trans (by simp)

private theorem augment_locus {r : ℕ} {t : ℝ} {A : Matrix I I K}
    (h : A ∈ rankSparseLocus I I K r t) (e : R ≃ I) (f : C ≃ I ⊕ I) :
    (fromCols (1 : Matrix I I K) Aᵀ).submatrix e f ∈
      rankSparseLocus R C K r (Fintype.card I + t) := by
  obtain ⟨B,Z,hB,hZ,rfl⟩ := h
  refine ⟨(fromCols (0 : Matrix I I K) Bᵀ).submatrix e f,
    (fromCols (1 : Matrix I I K) Zᵀ).submatrix e f, ?_, ?_, ?_⟩
  · rw [Matrix.rank_submatrix]
    have he : fromCols (0 : Matrix I I K) Bᵀ = Bᵀ * fromCols 0 (1 : Matrix I I K) := by
      rw [Matrix.mul_fromCols, Matrix.mul_zero, Matrix.mul_one]
    rw [he]
    apply (rank_mul_le_left _ _).trans
    rwa [rank_transpose]
  · rw [entryCount_submatrix, entryCount_augment, Nat.cast_add]
    exact add_le_add le_rfl hZ
  · ext i j
    cases hf : f j <;> simp [Matrix.submatrix_apply, hf]

theorem augment_sparse_border {r : ℕ} {t : ℝ} {A : Matrix I I K}
    (h : matrixPoint A ∈ affineZariskiClosure (matrixPoint '' rankSparseLocus I I K r t))
    (e : R ≃ I) (f : C ≃ I ⊕ I) :
    matrixPoint ((fromCols (1 : Matrix I I K) Aᵀ).submatrix e f) ∈
      affineZariskiClosure (matrixPoint '' rankSparseLocus R C K r (Fintype.card I + t)) := by
  let q (p : R × C) : MvPolynomial (I × I) K :=
    Sum.elim (fun j => MvPolynomial.C ((1 : Matrix I I K) (e p.1) j))
      (fun j => MvPolynomial.X (j,e p.1)) (f p.2)
  have he (M : Matrix I I K) :
      (fun p => MvPolynomial.eval (matrixPoint M) (q p)) =
        matrixPoint ((fromCols (1 : Matrix I I K) Mᵀ).submatrix e f) := by
    funext ⟨i,j⟩
    cases hf : f j <;> simp [matrixPoint, q, hf]
  rw [← he]
  apply mapsTo_affineZariskiClosure_of_polynomial q _ h
  rintro _ ⟨M,hM,rfl⟩
  exact ⟨_, augment_locus hM e f, (he M).symm⟩

variable {n J : ℕ}

private def timeRows (n J d : ℕ) :
    (Fin n × Fin (J*d)) ≃ ((Fin n × Fin J) × Fin d) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm).trans (Equiv.prodAssoc _ _ _).symm

private def timeCols (n J d : ℕ) :
    ((Fin n ⊕ Fin n) × Fin (J*d)) ≃
      (((Fin n × Fin J) × Fin d) ⊕ ((Fin n × Fin J) × Fin d)) :=
  (Equiv.sumProdDistrib _ _ _).trans (Equiv.sumCongr (timeRows n J d) (timeRows n J d))

private theorem augmented_repeat_eq {F : Type*} [Field F] (f : K →+* F)
    (B : Fin J → FourierBlock K n) (d : ℕ) :
    (fromCols (1 : Matrix ((Fin n × Fin J) × Fin d) _ F)
      (repeatTime d ((batchMatrix B).map f))ᵀ).submatrix (timeRows n J d) (timeCols n J d) =
    Matrix.blockDiagonal (fun jd : Fin (J*d) => blockInputOutput f (B (finProdFinEquiv.symm jd).1)) := by
  ext ⟨i,jd⟩ ⟨k,jd'⟩
  obtain ⟨⟨j,a⟩,rfl⟩ := (@finProdFinEquiv J d).surjective jd
  obtain ⟨⟨j',b⟩,rfl⟩ := (@finProdFinEquiv J d).surjective jd'
  rw [Matrix.blockDiagonal_apply', Equiv.symm_apply_apply]
  cases k <;> by_cases hj : j = j' <;> by_cases ha : a = b <;>
    simp [Matrix.blockDiagonal_apply, blockInputOutput,
      repeatTime, batchMatrix, timeCols, timeRows, Matrix.one_apply, hj, ha]
  grind

/-- The target list contains Jd independent blocks even though the error on
the original batch and all internal feedback wires can mix block indices. -/
theorem jointError_augmented_repeat (B : Fin J → FourierBlock K n) {S : ℕ} {r t : ℝ}
    (h : JointErrorBorderAtMost (batchMatrix B) S r t) (d : ℕ) :
    matrixPoint (Matrix.blockDiagonal (fun jd : Fin (J*d) =>
      blockInputOutput (algebraMap K (AlgebraicClosure K)) (B (finProdFinEquiv.symm jd).1))) ∈
    affineZariskiClosure (matrixPoint '' rankSparseLocus
      (Fin n × Fin (J*d)) ((Fin n ⊕ Fin n) × Fin (J*d)) (AlgebraicClosure K)
      (S + ⌊r⌋₊ * d) (((n:ℝ)*J)*d + repeatSupportBudget (n*J) d t)) := by
  rw [← augmented_repeat_eq]
  simpa using augment_sparse_border (jointError_repeated h d) (timeRows n J d) (timeCols n J d)

end
end FiniteFourier
end LinearAlgebra
end OAI
