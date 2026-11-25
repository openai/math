import OAI.LinearAlgebra.SpectralBooks.ArithmeticExponent
import OAI.LinearAlgebra.SpectralBooks.FormalPadding
import OAI.LinearAlgebra.SpectralBooks.FormalBlockStep
import OAI.LinearAlgebra.MatrixMultiplication.Rectangular.Growth

/-! # Formal circuit cost of powering a square rank decomposition -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic Foundation
noncomputable section

variable {F : Type*} [Field F]

private theorem formalCorrect_scalar : FormalCorrect (scalarAlgorithm F) := by
  intro i k
  fin_cases i
  fin_cases k
  change MvPolynomial.X (Sum.inl (0,0)) * MvPolynomial.X (Sum.inr (0,0)) = _
  simp

/-- Pad a program at each power to cover every positive size, retaining formal correctness. -/
private theorem squareAdmissible_of_power_costs {a : ℕ} (ha : 2 ≤ a) {τ : ℝ} (hτ : 0 ≤ τ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      ∃ P : MatrixAlgorithm F (a ^ t) (a ^ t) (a ^ t),
        FormalCorrect P ∧ (P.cost : ℝ) ≤ C * ((a : ℝ) ^ (τ + ε)) ^ t) :
    FormalAdmissibleExponent F 1 1 1 τ := by
  intro ε hε
  have ha' : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  obtain ⟨C, hC, hbound⟩ := h ε hε
  refine ⟨C * (a : ℝ) ^ (τ + ε), by positivity, ?_⟩
  intro N hN
  have hd : wireDimension N 1 = N := by simp [wireDimension]
  rw [hd]
  obtain ⟨t, hlow, hhigh⟩ := Foundation.Arithmetic.exists_power_cover ha hN
  obtain ⟨P, hP, hcost⟩ := hbound t
  refine ⟨P.pad hlow hlow hlow, hP.pad hlow hlow hlow, ?_⟩
  rw [MatrixAlgorithm.pad_cost_eq]
  apply hcost.trans
  calc
    _ = C * ((a ^ t : ℕ) : ℝ) ^ (τ + ε) := by rw [Nat.cast_pow, Real.rpow_pow_comm ha'.le]
    _ ≤ C * ((a : ℝ) * N) ^ (τ + ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hhigh) (by linarith)) hC.le
    _ = _ := by rw [Real.mul_rpow ha'.le (Nat.cast_nonneg _)]; ring

private theorem rpow_formalOmega_le_of_block_step {n R : ℕ} (hn : 2 ≤ n)
    (hR : n * n ≤ R)
    (hstep : ∀ (m : ℕ) (P : MatrixAlgorithm F m m m), FormalCorrect P →
      ∃ Q : MatrixAlgorithm F (n*m) (n*m) (n*m), FormalCorrect Q ∧
        Q.cost ≤ R * P.cost + 6 * R * n ^ 2 * m ^ 2) :
    (n : ℝ) ^ formalOmega F 1 1 1 ≤ R := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hR' : (0 : ℝ) < R := by
    exact_mod_cast (Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n)).trans_le hR
  let τ := Real.logb (n : ℝ) R
  have hrate : (n : ℝ) ^ τ = R := Real.rpow_logb (by linarith) hn'.ne' hR'
  have hτ : 0 ≤ τ := Real.logb_nonneg hn' (by exact_mod_cast (show 1 ≤ R by nlinarith))
  let K := 6 * R * n ^ 2
  have powers (t : ℕ) :
      ∃ P : MatrixAlgorithm F (n ^ t) (n ^ t) (n ^ t),
        FormalCorrect P ∧ P.cost ≤ rectangularBlockCost n n R K t := by
    induction t with
    | zero =>
      simpa using (show ∃ P : MatrixAlgorithm F 1 1 1, FormalCorrect P ∧ P.cost ≤ 1 from
        ⟨scalarAlgorithm F, formalCorrect_scalar, (scalarAlgorithm_cost F).le⟩)
    | succ t ih =>
      obtain ⟨P, hP, hcost⟩ := ih
      obtain ⟨Q, hQ, hrec⟩ := hstep (n^t) P hP
      rw [pow_succ']
      refine ⟨Q, hQ, hrec.trans ?_⟩
      apply Nat.add_le_add (Nat.mul_le_mul_left R hcost)
      change K * (n ^ t) ^ 2 ≤ K * ((n*n)^t + (n^2)^t)
      rw [← pow_mul, Nat.mul_comm t 2, pow_mul]
      exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  have hadm : FormalAdmissibleExponent F 1 1 1 τ := by
    apply squareAdmissible_of_power_costs hn hτ
    intro ε hε
    have hsize : ((n * n : ℕ) : ℝ) ≤ (n : ℝ) ^ τ := by rw [hrate]; exact_mod_cast hR
    obtain ⟨C, hC, hCbound⟩ := rectangularBlockCost_bound (b := n) (R := R) (K := K) hn hε
      hrate.ge hsize (by simpa [pow_two] using hsize)
    refine ⟨C, hC, fun t => ?_⟩
    obtain ⟨P, hP, hc⟩ := powers t
    exact ⟨P, hP, (Nat.cast_le.mpr hc).trans (hCbound t)⟩
  rw [← hrate]
  apply Real.rpow_le_rpow_of_exponent_le hn'.le
  exact csInf_le (s := {σ : ℝ | FormalAdmissibleExponent F 1 1 1 σ})
    ⟨loads 1 1 1 0, fun _ h => h.load_le 0⟩ hadm

/-- A fixed square rank decomposition bounds the formal arithmetic exponent
over an arbitrary field, including finite fields. -/
theorem rpow_formalOmega_le_tensorRank (F : Type*) [Field F] {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ formalOmega F 1 1 1 ≤ tensorRank (matrixTensor F n n n) := by
  apply rpow_formalOmega_le_of_block_step hn
  · exact (le_max_left _ _).trans (matrix_flattening_le_tensorRank F (by omega) (by omega) (by omega))
  · exact fun _ P hP => square_formal_block_step (rankAtMost_tensorRank _) P hP

end

end SpectralBooks
end LinearAlgebra
end OAI
