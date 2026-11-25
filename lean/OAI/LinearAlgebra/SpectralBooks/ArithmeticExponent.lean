import OAI.LinearAlgebra.SpectralBooks.Asymptotic
import OAI.LinearAlgebra.SpectralBooks.Circuit
import OAI.LinearAlgebra.SpectralBooks.Flattening

/-! # Rectangular arithmetic exponents over a field

The wire order is (12,23,31), so the product has dimensions
`(n31 × n12) × (n12 × n23)`. Correctness means polynomial identity over
the ground field, including when that field is finite.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Arithmetic

noncomputable section

/-- Admissible exponents for the rounded rectangular formats, with positive slack. -/
def FormalAdmissibleExponent (F : Type*) [Field F] (w12 w23 w31 τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    ∃ P : MatrixAlgorithm F (wireDimension N w31) (wireDimension N w12) (wireDimension N w23),
      FormalCorrect P ∧ (P.cost : ℝ) ≤ C * (N : ℝ) ^ (τ + ε)

/-- The arithmetic exponent in base size `N` at three prescribed wire weights. -/
def formalOmega (F : Type*) [Field F] (w12 w23 w31 : ℝ) : ℝ :=
  sInf {τ : ℝ | FormalAdmissibleExponent F w12 w23 w31 τ}

/-- The entrywise algorithm gives an admissible exponent in every weighted format. -/
theorem formalAdmissibleExponent_naive (F : Type*) [Field F] {w12 w23 w31 : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) :
    FormalAdmissibleExponent F w12 w23 w31 (w12 + w23 + w31) := by
  intro ε hε
  refine ⟨16, by norm_num, ?_⟩
  intro N hN
  refine ⟨Arithmetic.naiveAlgorithm _ _ _, formalCorrect_naiveAlgorithm F _ _ _, ?_⟩
  rw [Arithmetic.naiveAlgorithm_cost]
  push_cast
  have h : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  calc
    _ ≤ 2 * (2 * (N : ℝ) ^ w31) * (2 * (N : ℝ) ^ w12) * (2 * (N : ℝ) ^ w23) := by
      gcongr <;> apply wireDimension_le hN <;> assumption
    _ = 16 * (N : ℝ) ^ (w12 + w23 + w31) := by
      rw [Real.rpow_add (zero_lt_one.trans_le h), Real.rpow_add (zero_lt_one.trans_le h)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le h (le_add_of_nonneg_right hε.le)) (by norm_num)

/-- Positive slack allows the infimum itself as an admissible exponent. -/
theorem formalOmega_admissible (F : Type*) [Field F] {w12 w23 w31 : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) :
    FormalAdmissibleExponent F w12 w23 w31 (formalOmega F w12 w23 w31) := by
  intro ε hε
  let S := {τ : ℝ | FormalAdmissibleExponent F w12 w23 w31 τ}
  have hS : S.Nonempty := ⟨_, formalAdmissibleExponent_naive F h12 h23 h31⟩
  obtain ⟨τ, hτ, hclose⟩ := exists_lt_of_csInf_lt hS
    (lt_add_of_pos_right (sInf S) (half_pos hε))
  obtain ⟨C, hC, hbound⟩ := hτ (ε / 2) (half_pos hε)
  refine ⟨C, hC, fun N hN => ?_⟩
  obtain ⟨P, hP, hcost⟩ := hbound N hN
  refine ⟨P, hP, hcost.trans (mul_le_mul_of_nonneg_left ?_ hC.le)⟩
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
  change τ + ε / 2 ≤ sInf S + ε
  linarith

/-- A formal arithmetic cost bound also controls ordinary rank in each rounded format. -/
theorem FormalAdmissibleExponent.rank_growth {F : Type*} [Field F] {w12 w23 w31 τ : ℝ}
    (hτ : FormalAdmissibleExponent F w12 w23 w31 τ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (tensorRank (matrixTensor F (wireDimension N w12) (wireDimension N w23)
        (wireDimension N w31)) : ℝ) ≤ C * (N : ℝ) ^ (τ + ε) := by
  obtain ⟨C, hC, hc⟩ := hτ ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN
  obtain ⟨P, hP, hcost⟩ := hc N hN
  calc
    _ ≤ (2 : ℝ) * P.cost := by exact_mod_cast matrixTensor_rank_le_twice_cost hP
    _ ≤ 2 * (C * (N : ℝ) ^ (τ + ε)) := by linarith only [hcost]
    _ = _ := by ring

theorem matrixTensor_rank_pos (F : Type*) [Field F] {x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 0 < tensorRank (matrixTensor F x y z) :=
  (Nat.mul_pos hz hx).trans_le ((le_max_left _ _).trans (matrix_flattening_le_tensorRank F hx hy hz))

/-- Each logarithmic site load is a lower bound on the ordinary log-rank. -/
theorem matrix_load_le_log_tensorRank (F : Type*) [Field F] {x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (i : Fin 3) :
    loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z) i ≤
      Real.logb 2 (tensorRank (matrixTensor F x y z)) := by
  let r := tensorRank (matrixTensor F x y z)
  have hlog {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hprod : a * b ≤ r) :
      Real.logb 2 a + Real.logb 2 b ≤ Real.logb 2 r := by
    rw [← Real.logb_mul (by positivity : (a : ℝ) ≠ 0) (by positivity : (b : ℝ) ≠ 0)]
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    exact_mod_cast hprod
  obtain ⟨h₁, h₂, h₃⟩ := (max_le_iff.mp (matrix_flattening_le_tensorRank F hx hy hz)).imp_right
    max_le_iff.mp
  fin_cases i
  · exact hlog hz hx h₁
  · exact hlog hx hy h₂
  · exact hlog hy hz h₃

/-- Every formal rectangular arithmetic exponent dominates each local dimension exponent. -/
theorem FormalAdmissibleExponent.load_le {F : Type*} [Field F] {w12 w23 w31 τ : ℝ}
    (hτ : FormalAdmissibleExponent F w12 w23 w31 τ) (i : Fin 3) : loads w12 w23 w31 i ≤ τ := by
  apply le_of_dyadic_log_bound
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ.rank_growth ε hε
  refine ⟨C, hC, fun k => ?_⟩
  have hdim (w : ℝ) := wireDimension_pos (N := 2 ^ k) (by positivity) w
  apply (dyadic_load_le k _ _ _ i).trans
  apply (matrix_load_le_log_tensorRank F (hdim w12) (hdim w23) (hdim w31) i).trans
  exact Real.logb_le_logb_of_le (by norm_num)
    (by exact_mod_cast matrixTensor_rank_pos F (hdim w12) (hdim w23) (hdim w31))
    (hbound _ (Nat.one_le_pow _ _ (by decide)))

theorem load_le_formalOmega (F : Type*) [Field F] {w12 w23 w31 : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) (i : Fin 3) :
    loads w12 w23 w31 i ≤ formalOmega F w12 w23 w31 :=
  (formalOmega_admissible F h12 h23 h31).load_le i

@[simp] theorem unit_weight_loads : loads 1 1 1 = fun _ => 2 := by
  funext i
  fin_cases i <;> norm_num [loads]

private theorem loads_nonnegative {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    ∀ i, 0 ≤ loads u v w i := by
  intro i
  fin_cases i <;> dsimp [loads] <;> positivity

section RankBound

variable {F : Type*} [Field F]
variable (hfinite : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
  RadicalTest (loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z))
    (Real.logb 2 (tensorRank (matrixTensor F x y z))))

include hfinite

private theorem heightTest_of_matrix_rank_growth {w12 w23 w31 τ : ℝ}
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (tensorRank (matrixTensor F (wireDimension N w12) (wireDimension N w23)
        (wireDimension N w31)) : ℝ) ≤ C * (N : ℝ) ^ (τ + ε)) :
    HeightTest (loads w12 w23 w31) τ := by
  apply heightTest_of_polynomial_bound
  intro ε hε
  obtain ⟨C, hC, hc⟩ := hgrowth ε hε
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hdim (w : ℝ) := wireDimension_pos (N := N) (by omega) w
  have hlog (w : ℝ) : 0 ≤ Real.logb 2 (wireDimension N w) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hdim w)
  have htest := (hfinite _ _ _ (hdim w12) (hdim w23) (hdim w31)).heightTest
    (loads_nonnegative (hlog _) (hlog _) (hlog _))
  apply htest.mono
  exact Real.logb_le_logb_of_le (by norm_num)
    (by exact_mod_cast matrixTensor_rank_pos F (hdim w12) (hdim w23) (hdim w31)) (hc N hN)

/-- Take the infimum over all polynomial growth bounds supplied by a circuit model.
The rank may be measured over a common extension of its field of constants. -/
theorem radicalTest_sInf_of_matrix_rank_growth {w12 w23 w31 : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) {S : Set ℝ} (hS : S.Nonempty)
    (hgrowth : ∀ τ ∈ S, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (tensorRank (matrixTensor F (wireDimension N w12) (wireDimension N w23)
        (wireDimension N w31)) : ℝ) ≤ C * (N : ℝ) ^ (τ + ε)) :
    RadicalTest (loads w12 w23 w31) (sInf S) :=
  (heightTest_sInf hS fun τ hτ => heightTest_of_matrix_rank_growth hfinite (hgrowth τ hτ)).radicalTest
    (loads_nonnegative h12 h23 h31)

/-- The finite ordinary-rank inequality gives the rectangular arithmetic exponent inequality. -/
theorem formalOmega_radicalTest_of_rank_bound {w12 w23 w31 : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) :
    RadicalTest (loads w12 w23 w31) (formalOmega F w12 w23 w31) := by
  apply radicalTest_sInf_of_matrix_rank_growth hfinite h12 h23 h31
    (S := {τ | FormalAdmissibleExponent F w12 w23 w31 τ}) ⟨_, formalAdmissibleExponent_naive F h12 h23 h31⟩
  exact fun _ hτ => hτ.rank_growth

/-- The square exponent consequence of the finite ordinary-rank inequality. -/
theorem formalOmega_square_lower_bound_of_rank_bound :
    3 / Real.sqrt 2 ≤ formalOmega F 1 1 1 := by
  apply square_lower_bound
  simpa only [unit_weight_loads] using formalOmega_radicalTest_of_rank_bound hfinite
    (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)

end RankBound
end

end SpectralBooks
end LinearAlgebra
end OAI
