import OAI.LinearAlgebra.FiniteFourier.Batched
import OAI.LinearAlgebra.FiniteFourier.CircuitToFeedback

/-! # A linear lower bound with unrestricted mixing between the blocks

Two marked nonzero entries in each output row exclude every direct input readout.
The determinant then counts independent state readouts. A single polynomial witnesses
both conditions, so the estimate survives joint degeneration of the feedback weights.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier
open Matrix MvPolynomial
noncomputable section

private theorem reindexed_det_ne_zero {K I O T : Type*} [Field K] [Fintype I]
    [Fintype O] [Fintype T] [DecidableEq T] [DecidableEq O]
    (A : Matrix O I K) (D : Matrix I O K) (h : A * D = 1) (o : T ≃ O) (i : T ≃ I) :
    (A.submatrix o i).det ≠ 0 := by
  have he : A.submatrix o i * D.submatrix i o = 1 := by
    rw [submatrix_mul_equiv, h, submatrix_one_equiv]
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_one] at hd
  exact left_ne_zero_of_mul_eq_one hd

theorem FourierBlock.det_ne_zero {K : Type*} [Field K] {n : ℕ} (B : FourierBlock K n) :
    B.matrix.det ≠ 0 := by
  classical
  unfold FourierBlock.matrix
  split
  · exact reindexed_det_ne_zero _ _ (inverse_mul_fourier B.G K B.admissible) B.points B.frequencies
  · exact reindexed_det_ne_zero _ _ (fourier_mul_inverse B.G K B.admissible) B.frequencies B.points

theorem FourierBlock.entry_ne_zero {K : Type*} [Field K] {n : ℕ} (B : FourierBlock K n)
    (a b : Fin n) : B.matrix a b ≠ 0 := by
  unfold FourierBlock.matrix
  split
  · exact mul_ne_zero (inv_ne_zero B.admissible.1) (Units.ne_zero _)
  · exact Units.ne_zero _

private theorem Feedback.rank_le_of_two_entries {K I : Type*} [Field K] [Fintype I]
    {s : ℕ} (F : Feedback K I I s) (a b : I → I) (hab : ∀ i, a i ≠ b i)
    (ha : ∀ i, F.matrix i (a i) ≠ 0) (hb : ∀ i, F.matrix i (b i) ≠ 0) :
    F.matrix.rank ≤ s := by
  classical
  have read : F.readInput = 0 := by
    ext o i
    cases hout : F.output o with
    | zero => simp [Feedback.readInput, Feedback.readRow, hout]
    | scaled c w =>
      cases w with
      | inr => simp [Feedback.readInput, Feedback.readRow, hout]
      | inl k =>
        have vanish (j : I) (hj : k ≠ j) : F.matrix o j = 0 := by
          have h := F.matrix_mulVec_apply (Pi.single j 1) o
          simpa [hout, Matrix.mulVec_single, Pi.single_apply, hj] using h
        by_cases h : k = a o
        · exact False.elim (hb o (vanish _ (h ▸ hab o)))
        · exact False.elim (ha o (vanish _ h))
  rw [Feedback.matrix, read, zero_add]
  exact (Matrix.rank_mul_le_left _ _).trans
    (by simpa using (F.readState * (1 - F.stateMatrix)⁻¹).rank_le_card_width)

/-- A nonsingular square matrix with two nonzero entries in each row requires one
state per output, even in geometric border. Off-block entries may vanish. -/
theorem GeometricBorderAtMost.card_le_of_two_entries {K I : Type*} [Field K] [Fintype I]
    [DecidableEq I] {M : Matrix I I K} {s : ℕ} (hm : GeometricBorderAtMost M s)
    (hd : M.det ≠ 0) (a b : I → I) (hab : ∀ i, a i ≠ b i)
    (ha : ∀ i, M i (a i) ≠ 0) (hb : ∀ i, M i (b i) ≠ 0) : Fintype.card I ≤ s := by
  classical
  by_contra! hs
  let L := AlgebraicClosure K
  let P : Matrix I I (MvPolynomial (I × I) L) := fun i j => X (i,j)
  let p : MvPolynomial (I × I) L := P.det * (∏ i, X (i, a i)) * ∏ i, X (i, b i)
  have ev (A : Matrix I I L) :
      eval (fun ij => A ij.1 ij.2) p = A.det * (∏ i, A i (a i)) * ∏ i, A i (b i) := by
    simp only [p, map_mul, map_prod, eval_X]
    have hm : (eval (fun ij : I × I => A ij.1 ij.2)).mapMatrix P = A := by
      ext i j
      change eval (fun ij : I × I => A ij.1 ij.2) (X (i, j)) = A i j
      simp
    rw [RingHom.map_det, hm]
  have h := hm p (by
    rintro A ⟨r, hrs, F, _, rfl⟩
    rw [ev]
    by_contra hn
    have h1 := (mul_ne_zero_iff.mp hn)
    have h2 := mul_ne_zero_iff.mp h1.1
    have hr := F.rank_le_of_two_entries a b hab
      (fun i => Finset.prod_ne_zero_iff.mp h2.2 i (Finset.mem_univ i))
      (fun i => Finset.prod_ne_zero_iff.mp h1.2 i (Finset.mem_univ i))
    rw [Matrix.rank_of_det_ne_zero h2.1] at hr
    omega)
  let f := algebraMap K L
  change eval (fun ij => (M.map f) ij.1 ij.2) p = 0 at h
  have hdet : (M.map f).det = f M.det := (f.map_det M).symm
  rw [ev, hdet] at h
  refine (mul_ne_zero (mul_ne_zero ((map_ne_zero_iff f f.injective).mpr hd)
    (Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero_iff f f.injective).mpr (ha i)))
    (Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero_iff f f.injective).mpr (hb i))) h

theorem batchFourier_border_card_le {K : Type*} [Field K] {J n s : ℕ}
    (B : Fin J → FourierBlock K n) (hn : 2 ≤ n) (h : GeometricBorderAtMost (batchMatrix B) s) :
    J * n ≤ s := by
  classical
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hd : (batchMatrix B).det ≠ 0 := by
    rw [batchMatrix, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => (B j).det_ne_zero
  have entry (o : Fin n × Fin J) (i : Fin n) : batchMatrix B o (i, o.2) ≠ 0 := by
    simpa [batchMatrix, Matrix.blockDiagonal_apply] using (B o.2).entry_ne_zero o.1 i
  have hr := h.card_le_of_two_entries hd (fun o => (i₀, o.2)) (fun o => (i₁, o.2))
    (fun o he => by have := congrArg (fun x : Fin n × Fin J => x.1.val) he; simp [i₀, i₁] at this)
    (fun o => entry o i₀) (fun o => entry o i₁)
  simpa [Nat.mul_comm] using hr

theorem batchFourier_card_le {K : Type*} [Field K] {J n : ℕ}
    (B : Fin J → FourierBlock K n) (hn : 2 ≤ n) : J * n ≤ complexity (batchMatrix B) :=
  batchFourier_border_card_le B hn (realizableAtMost_complexity _).geometricBorder

end
end FiniteFourier
end LinearAlgebra
end OAI
