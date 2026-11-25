import OAI.LinearAlgebra.SpectralBooks.SquareExponent
import OAI.LinearAlgebra.SpectralBooks.CircuitRankSpecialization

/-! # The lower bound for circuits allowing division

For quotient gates, rank is controlled after extending scalars to the
algebraic closure. The finite rank bound there can therefore be used for
circuits defined over the original ground field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

/-- Admissible arithmetic exponents when division by nonzero rational functions is allowed. -/
def DivisionAdmissibleExponent (F : Type*) [Field F] (w12 w23 w31 τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    ∃ P : RationalMatrixAlgorithm F (wireDimension N w31) (wireDimension N w12) (wireDimension N w23),
      P.Correct ∧ (P.cost : ℝ) ≤ C * (N : ℝ) ^ (τ + ε)

/-- The arithmetic exponent with division gates. -/
def divisionOmega (F : Type*) [Field F] (w12 w23 w31 : ℝ) : ℝ :=
  sInf {τ : ℝ | DivisionAdmissibleExponent F w12 w23 w31 τ}

theorem FormalAdmissibleExponent.toDivision {F : Type*} [Field F] {w12 w23 w31 τ : ℝ}
    (hτ : FormalAdmissibleExponent F w12 w23 w31 τ) :
    DivisionAdmissibleExponent F w12 w23 w31 τ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  refine ⟨C, hC, fun N hN => ?_⟩
  obtain ⟨P, hP, hcost⟩ := hbound N hN
  exact ⟨.ofDivisionFree P, RationalMatrixAlgorithm.correct_ofDivisionFree hP, by simpa using hcost⟩

section RankBound

variable {F : Type*} [Field F]
variable (hfinite : ∀ (x y z : ℕ), 0 < x → 0 < y → 0 < z →
  RadicalTest (loads (Real.logb 2 x) (Real.logb 2 y) (Real.logb 2 z))
    (Real.logb 2 (tensorRank (matrixTensor (AlgebraicClosure F) x y z))))

theorem DivisionAdmissibleExponent.rank_growth {w12 w23 w31 τ : ℝ}
    (hτ : DivisionAdmissibleExponent F w12 w23 w31 τ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (tensorRank (matrixTensor (AlgebraicClosure F) (wireDimension N w12) (wireDimension N w23)
        (wireDimension N w31)) : ℝ) ≤ C * (N : ℝ) ^ (τ + ε) := by
  obtain ⟨C, hC, hc⟩ := hτ ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN
  obtain ⟨P, hP, hPCost⟩ := hc N hN
  calc
    _ ≤ (2 : ℝ) * P.cost := by exact_mod_cast algebraicClosure_rank_le_twice_cost hP
    _ ≤ 2 * (C * (N : ℝ) ^ (τ + ε)) := by linarith only [hPCost]
    _ = _ := by ring

include hfinite

/-- The rectangular radical test for division circuits follows from the finite rank bound
over the algebraic closure. -/
theorem divisionOmega_radicalTest_of_rank_bound {w12 w23 w31 : ℝ}
    (h12 : 0 ≤ w12) (h23 : 0 ≤ w23) (h31 : 0 ≤ w31) :
    RadicalTest (loads w12 w23 w31) (divisionOmega F w12 w23 w31) := by
  apply radicalTest_sInf_of_matrix_rank_growth hfinite h12 h23 h31
    (S := {τ | DivisionAdmissibleExponent F w12 w23 w31 τ})
    ⟨_, (formalAdmissibleExponent_naive F h12 h23 h31).toDivision⟩
  exact fun _ hτ => DivisionAdmissibleExponent.rank_growth hτ

theorem divisionOmega_square_lower_bound_of_rank_bound :
    3 / Real.sqrt 2 ≤ divisionOmega F 1 1 1 := by
  apply square_lower_bound
  simpa only [unit_weight_loads] using divisionOmega_radicalTest_of_rank_bound hfinite
    (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)

end RankBound

/-- Division by nonzero rational functions does not change the square arithmetic
exponent over any field. A quotient circuit controls rank over the algebraic
closure. Tensor powers recover the ground-field exponent from that rank bound. -/
theorem divisionOmega_square_eq_formalOmega (F : Type*) [Field F] :
    divisionOmega F 1 1 1 = formalOmega F 1 1 1 := by
  let S := {τ : ℝ | DivisionAdmissibleExponent F 1 1 1 τ}
  have hω : DivisionAdmissibleExponent F 1 1 1 (formalOmega F 1 1 1) :=
    (formalOmega_admissible F (by norm_num) (by norm_num) (by norm_num)).toDivision
  have hlower (τ : ℝ) (hτ : τ ∈ S) : formalOmega F 1 1 1 ≤ τ := by
    apply (Real.rpow_le_rpow_left_iff (show (1 : ℝ) < 2 by norm_num)).mp
    have h := square_asymptoticRank_le_of_rank_growth (AlgebraicClosure F) (n := 2)
      (by decide) (DivisionAdmissibleExponent.rank_growth hτ)
    rw [asymptoticRank_matrixTensor_baseChange F (AlgebraicClosure F),
      square_asymptoticRank_eq_rpow_formalOmega F (by decide)] at h
    exact h
  exact le_antisymm (csInf_le (s := S) ⟨_, fun τ hτ => hlower τ hτ⟩ hω)
    (le_csInf (s := S) ⟨_, hω⟩ hlower)

end

end SpectralBooks
end LinearAlgebra
end OAI
