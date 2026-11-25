import OAI.LinearAlgebra.FiniteFourier.BatchedBorderQuotient
import OAI.LinearAlgebra.FiniteFourier.BatchedEchelon
import OAI.LinearAlgebra.FiniteFourier.BatchedListBlocks
import OAI.LinearAlgebra.FiniteFourier.BatchedListSpecialization
import OAI.LinearAlgebra.FiniteFourier.BatchedListCount

/-! # A single rank and support budget for independent lists -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical NNReal

variable {K : Type*} [Field K] {R C : Type} [Fintype R] [Fintype C] {J : ℕ}
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop))

theorem exists_diagonal_list_quotients [Infinite K] (U : Fin J → Matrix R C K)
    (Q : Matrix (R × Fin J) (R × Fin J) K) :
    ∃ D : Fin J → Matrix R R K, (∑ i, (D i).rank) = Q.rank ∧
      ∑ i, listValue φ (D i * U i) ≤ listValue φ (Q * Matrix.blockDiagonal U) := by
  obtain ⟨L, htri, hsum⟩ := exists_echelon_left_factor Q
  let D (i : Fin J) := (L * Q).submatrix (fun a => (a,i)) (fun b => (b,i))
  let A := (L * Q) * Matrix.blockDiagonal U
  have he (a : R) (b : C) (i j : Fin J) :
      A (a,i) (b,j) = ∑ t, (L * Q) (a,i) (t,j) * U j t b := by
    simp [A, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.blockDiagonal_apply, mul_ite]
  have hupper : ∀ (p : R × Fin J) (q : C × Fin J), q.2.val < p.2.val → A p q = 0 := by
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    rw [he]
    exact Finset.sum_eq_zero (fun t _ => by rw [htri a t i j h, zero_mul])
  have hdiag := listValue_diagonalBlocks_le φ A (fun p => p.2.val) (fun q => q.2.val) hupper
  have heq : Matrix.of (fun (p : R × Fin J) (q : C × Fin J) =>
      if p.2.val = q.2.val then A p q else 0) = Matrix.blockDiagonal (fun i => D i * U i) := by
    ext ⟨a,i⟩ ⟨b,j⟩
    by_cases hij : i = j
    · subst j
      simp only [Matrix.of_apply, Matrix.blockDiagonal_apply_eq, he]
      rfl
    · simp [Matrix.blockDiagonal_apply, hij, Fin.val_inj]
  rw [heq, listValue_blockDiagonal] at hdiag
  refine ⟨D, hsum, hdiag.trans ?_⟩
  unfold A
  rw [Matrix.mul_assoc]
  exact listValue_mul_le φ L _

theorem sparse_border_block_quotients [IsAlgClosed K] [Nonempty R] [Nonempty (Fin J)]
    (P : SpectralPlacementPrices K Plane)
    (hflat : ∀ (s : Finset Plane) (hs : s.Nonempty), P.diagonal s = meanWidth s hs)
    {x a b : Plane} {δ : ℝ} (hp : PricesListsAt P φ x a b δ) (hd : 0 < δ)
    (hlen : dist a b ≤ δ) (r : ℕ) (T : ℝ) (hT : 0 ≤ T) (U : Fin J → Matrix R C K)
    (hM : matrixPoint (Matrix.blockDiagonal U) ∈ affineZariskiClosure
      (matrixPoint '' rankSparseLocus (R × Fin J) (C × Fin J) K r T)) :
    ∃ D : Fin J → Matrix R R K,
      (∑ i, (Fintype.card R - (D i).rank)) ≤ r ∧
      (∑ i, (listValue φ (D i * U i) : ℝ)) ≤ (J * (Fintype.card R : ℝ)) *
        (T / (J * (Fintype.card R : ℝ))) ^ (dist a b / δ) := by
  obtain ⟨Q, hQ, hv⟩ := exists_row_quotient_of_sparse_border φ P hflat hp hd hlen r T hT _ hM
  obtain ⟨D, hD, hsum⟩ := exists_diagonal_list_quotients φ U Q
  have hcard : Fintype.card (R × Fin J) = J * Fintype.card R := by simp [mul_comm]
  rw [hcard] at hQ hv
  refine ⟨D, ?_, ?_⟩
  · have he : (∑ i, (Fintype.card R - (D i).rank)) + Q.rank = J * Fintype.card R := by
      rw [← hD, ← Finset.sum_add_distrib]
      simp [Nat.sub_add_cancel (Matrix.rank_le_card_height _)]
    omega
  · rw [← NNReal.coe_sum]
    push_cast at hv
    exact (NNReal.coe_le_coe.mpr hsum).trans hv

theorem sparse_border_obstruction [IsAlgClosed K] [Nonempty R] [Nonempty (Fin J)]
    (P : SpectralPlacementPrices K Plane)
    (hflat : ∀ (s : Finset Plane) (hs : s.Nonempty), P.diagonal s = meanWidth s hs)
    {x a b : Plane} {δ ε : ℝ} (hp : PricesListsAt P φ x a b δ) (hd : 0 < δ)
    (hlen : dist a b ≤ δ) (he : 0 < ε) (r : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (U : Fin J → Matrix R C K)
    (detect : ∀ i (Q : Matrix R R K), ((Fintype.card R - Q.rank : ℕ) : ℝ) ≤
      ε * Fintype.card R → (9/5 : ℝ) * Fintype.card R ≤ listValue φ (Q * U i))
    (rankBudget : (r : ℝ) ≤ ε * (J * (Fintype.card R : ℝ)) / 200)
    (supportBudget : (T / (J * (Fintype.card R : ℝ))) ^ (dist a b / δ) ≤ 179/100) :
    matrixPoint (Matrix.blockDiagonal U) ∉ affineZariskiClosure
      (matrixPoint '' rankSparseLocus (R × Fin J) (C × Fin J) K r T) := by
  intro hM
  obtain ⟨D, hloss, hval⟩ := sparse_border_block_quotients φ P hflat hp hd hlen r T hT U hM
  apply projected_list_obstruction (n := Fintype.card R) (by positivity) he
    (fun i => ((Fintype.card R - (D i).rank : ℕ) : ℝ))
    (fun i => (listValue φ (D i * U i) : ℝ)) (fun _ => by positivity)
    (fun _ => NNReal.coe_nonneg _) _ (fun i => detect i (D i))
  · rw [Fintype.card_fin, mul_comm (179/100 : ℝ)]
    exact hval.trans (mul_le_mul_of_nonneg_left supportBudget (by positivity))
  · rw [Fintype.card_fin]
    apply le_trans _ rankBudget
    exact_mod_cast hloss

end FiniteFourier
end LinearAlgebra
end OAI
