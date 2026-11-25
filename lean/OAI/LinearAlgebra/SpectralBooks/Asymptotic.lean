import OAI.LinearAlgebra.SpectralBooks.Rank
import OAI.LinearAlgebra.SpectralBooks.Scaling

/-! # From finite height bounds to arithmetic exponents

Evaluate the finite bound at base sizes `2 ^ k`. Rounding each dimension
up only increases its logarithmic load. The logarithm of a constant in
a polynomial cost bound contributes a fixed additive term, which disappears
when the inequality holds at every dyadic scale.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators

noncomputable section

/-- Logarithmic site loads at the three rounded wire dimensions of base size `N`. -/
def scaledLoads (N : ℕ) (w12 w23 w31 : ℝ) : Fin 3 → ℝ :=
  loads (Real.logb 2 (wireDimension N w12)) (Real.logb 2 (wireDimension N w23))
    (Real.logb 2 (wireDimension N w31))

/-- The dyadic loads dominate the real weights multiplied by the scale exponent. -/
theorem dyadic_load_le (k : ℕ) (w12 w23 w31 : ℝ) (i : Fin 3) :
    (k : ℝ) * loads w12 w23 w31 i ≤ scaledLoads (2 ^ k) w12 w23 w31 i := by
  fin_cases i <;> dsimp [scaledLoads, loads] <;> rw [mul_add] <;>
    exact add_le_add (dyadic_wireDimension_log_ge _ _) (dyadic_wireDimension_log_ge _ _)

/-- A uniform polynomial bound at dyadic scales forces the growth exponent
to dominate the slope, independently of the multiplicative constant. -/
theorem le_of_dyadic_log_bound {u τ : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      (k : ℝ) * u ≤ Real.logb 2 (C * ((2 ^ k : ℕ) : ℝ) ^ (τ + ε))) : u ≤ τ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨C, hC, hk⟩ := h ε hε
  by_contra! hlt
  obtain ⟨k, hlarge⟩ := exists_lt_nsmul (sub_pos.mpr hlt) (Real.logb 2 C)
  rw [nsmul_eq_mul] at hlarge
  have hbound := hk k
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_mul hC.ne' (by positivity),
    Real.logb_rpow_eq_mul_logb_of_pos (by positivity), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one] at hbound
  nlinarith only [hlarge, hbound]

/-- A polynomial upper bound on the finite height-test parameter implies
the corresponding test on exponent loads, with all positive slack removed. -/
theorem heightTest_of_polynomial_bound {w12 w23 w31 τ : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      HeightTest (scaledLoads N w12 w23 w31) (Real.logb 2 (C * (N : ℝ) ^ (τ + ε)))) :
    HeightTest (loads w12 w23 w31) τ := by
  intro a ha
  let M := ∑ i, a i * loads w12 w23 w31 i
  let D := ∑ i, Real.sqrt (1 + a i ^ 2) - 1
  have hD : 0 < D := heightDenom_pos a
  change M ≤ τ * D
  apply (div_le_iff₀ hD).mp
  apply le_of_dyadic_log_bound
  intro ε hε
  obtain ⟨C, hC, hN⟩ := h ε hε
  refine ⟨C, hC, fun k => ?_⟩
  rw [← mul_div_assoc, div_le_iff₀ hD]
  have hstep : (k : ℝ) * M ≤ ∑ i, a i * scaledLoads (2 ^ k) w12 w23 w31 i := by
    dsimp only [M]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (dyadic_load_le k _ _ _ i) (ha i).le
  exact hstep.trans (hN (2 ^ k) (Nat.one_le_pow _ _ (by decide)) a ha)

/-- Height tests pass to the infimum of any nonempty set of admissible exponents. -/
theorem heightTest_sInf {m : Fin 3 → ℝ} {S : Set ℝ} (hS : S.Nonempty)
    (h : ∀ τ ∈ S, HeightTest m τ) : HeightTest m (sInf S) := by
  intro a ha
  have hD := heightDenom_pos a
  apply (div_le_iff₀ hD).mp
  exact le_csInf hS fun τ hτ => (div_le_iff₀ hD).mpr (h τ hτ a ha)

end

end SpectralBooks
end LinearAlgebra
end OAI
