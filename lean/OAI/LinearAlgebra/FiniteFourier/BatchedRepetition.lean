import OAI.LinearAlgebra.FiniteFourier.BatchedDelay
import OAI.LinearAlgebra.FiniteFourier.BatchedBorderQuotient
import OAI.LinearAlgebra.SpectralBooks.KroneckerRank

/-! # Repetition of a joint geometric border point -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix OAI.LinearAlgebra.SpectralBooks
open scoped Classical Kronecker
noncomputable section

variable {K : Type*} [Field K] {I O : Type} [Fintype O] [Fintype I]

theorem entryCount_sum (A : Matrix O I K) :
    matrixEntryCount A = ∑ o, ∑ i, if A o i ≠ 0 then 1 else 0 := by
  simp only [matrixEntryCount_eq_sum, Finset.card_filter]

theorem entryCount_add_le (A B : Matrix O I K) :
    matrixEntryCount (A+B) ≤ matrixEntryCount A + matrixEntryCount B := by
  rw [entryCount_sum, entryCount_sum, entryCount_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro o _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Matrix.add_apply]
  by_cases ha : A o i = 0 <;> by_cases hb : B o i = 0 <;> simp [ha,hb]
  split <;> omega

def repeatTime {R : Type*} [Zero R] (d : ℕ) (A : Matrix O I R) :=
  Matrix.blockDiagonal (fun _ : Fin d => A)

theorem repeatTime_rank (d : ℕ) (A : Matrix O I K) :
    (repeatTime d A).rank = A.rank * d := by
  have he : repeatTime d A = A ⊗ₖ (1 : Matrix (Fin d) (Fin d) K) := by
    ext ⟨o,a⟩ ⟨i,b⟩
    simp [repeatTime, Matrix.blockDiagonal_apply', Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [he, rank_kronecker, Matrix.rank_one, Fintype.card_fin]

theorem repeatTime_count (d : ℕ) (A : Matrix O I K) :
    matrixEntryCount (repeatTime d A) = matrixEntryCount A * d := by
  rw [entryCount_sum, entryCount_sum, Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro o _
  have he (a : Fin d) :
      (∑ ib : I × Fin d, if repeatTime d A (o,a) ib ≠ 0 then 1 else 0) =
      ∑ i, if A o i ≠ 0 then 1 else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single a]
    · simp [repeatTime]
    · intro b _ hb
      simp [repeatTime, Matrix.blockDiagonal_apply', Ne.symm hb]
    · simp
  simp_rw [he]
  simp [mul_comm]

def repeatSupportBudget (h d : ℕ) (t : ℝ) :=
  ((h:ℝ)*d) * ((d:ℝ) * 2^d * d) + t*d

private theorem repeat_regular [Infinite K] {A B Z : Matrix O I K} {S : ℕ} {r t : ℝ}
    (hA : FeedbackAtMost A S) (hB : (B.rank:ℝ) ≤ r) (hZ : (matrixEntryCount Z:ℝ) ≤ t)
    (d : ℕ) :
    matrixPoint (repeatTime d (A+B+Z)) ∈ affineZariskiClosure (matrixPoint ''
      rankSparseLocus (O × Fin d) (I × Fin d) K (S + ⌊r⌋₊ * d)
        (repeatSupportBudget (Fintype.card O) d t)) := by
  obtain ⟨s, hs, F, hF, rfl⟩ := hA
  let e : Fin d → K := fun a => Infinite.natEmbedding K a.val
  let nodes (x : K) (a : Fin d) := 1 + x * e a
  let curve (x : K) := Matrix.blockDiagonal (fun a => delayNumerator F (nodes x a)) +
    repeatTime d B + repeatTime d Z
  have heq : repeatTime d (F.matrix+B+Z) = curve 0 := by
    ext ⟨o,a⟩ ⟨i,b⟩
    by_cases h : a = b <;>
      simp [repeatTime, curve, Matrix.blockDiagonal_apply', h, nodes, delayNumerator_one F hF]
  rw [heq]
  let c (q : (O × Fin d) × (I × Fin d)) : Polynomial K :=
    if q.1.2 = q.2.2 then
      Polynomial.C (F.transferDenom.eval 1)⁻¹ *
        (F.transferNumer q.1.1 q.2.1).comp (1 + Polynomial.X * Polynomial.C (e q.1.2)) +
      Polynomial.C (B q.1.1 q.2.1) + Polynomial.C (Z q.1.1 q.2.1)
    else 0
  have hc (x : K) : (fun q => (c q).eval x) = matrixPoint (curve x) := by
    funext ⟨⟨o,a⟩,i,b⟩
    by_cases h : a = b <;>
      simp [c, matrixPoint, curve, repeatTime, Matrix.blockDiagonal_apply', h,
        delayNumerator, Polynomial.eval_comp, nodes, mul_comm x]
  rw [← hc]
  apply polynomialCurve_zero_mem_affineZariskiClosure
  intro x hx
  rw [hc]
  have hinj : Function.Injective (nodes x) := by
    intro a b hab
    exact Fin.ext ((Infinite.natEmbedding K).injective
      (mul_left_cancel₀ hx (add_left_cancel hab)))
  obtain ⟨U,V,hU,hV,he⟩ := delay_rank_support F _ hinj
  refine ⟨curve x, ⟨U + repeatTime d B, V + repeatTime d Z, ?_, ?_, ?_⟩, rfl⟩
  · apply (matrix_rank_add_le _ _).trans
    rw [repeatTime_rank]
    exact Nat.add_le_add (hU.trans hs) (Nat.mul_le_mul_right d (Nat.le_floor hB))
  · apply le_trans (Nat.cast_le.mpr (entryCount_add_le _ _))
    rw [repeatTime_count, Nat.cast_add, Nat.cast_mul]
    unfold repeatSupportBudget
    exact add_le_add (by exact_mod_cast hV) (mul_le_mul_of_nonneg_right hZ (by positivity))
  · unfold curve
    rw [he]
    abel

/-- Repeat the entire joint border point, including cross-block errors. The
feedback state budget is charged once and the two error budgets scale by d. -/
theorem jointError_repeated {M : Matrix O I K} {S : ℕ} {r t : ℝ}
    (h : JointErrorBorderAtMost M S r t) (d : ℕ) :
    matrixPoint (repeatTime d (M.map (algebraMap K (AlgebraicClosure K)))) ∈
      affineZariskiClosure (matrixPoint '' rankSparseLocus
        (O × Fin d) (I × Fin d) (AlgebraicClosure K) (S + ⌊r⌋₊ * d)
        (repeatSupportBudget (Fintype.card O) d t)) := by
  let f (q : (O × Fin d) × (I × Fin d)) : MvPolynomial (O × I) (AlgebraicClosure K) :=
    if q.1.2 = q.2.2 then MvPolynomial.X (q.1.1, q.2.1) else 0
  have he (A : Matrix O I (AlgebraicClosure K)) :
      matrixPoint (repeatTime d A) = MvPolynomial.eval (matrixPoint A) ∘ f := by
    funext ⟨⟨o,a⟩,i,b⟩
    by_cases hab : a = b <;> simp [matrixPoint, repeatTime, Matrix.blockDiagonal_apply', f, hab]
  intro p hp
  rw [he, MvPolynomial.eval_assoc]
  apply h
  intro A B Z hA hB hZ
  have hz := repeat_regular hA hB hZ d p hp
  rw [he, MvPolynomial.eval_assoc] at hz
  exact hz

end
end FiniteFourier
end LinearAlgebra
end OAI
