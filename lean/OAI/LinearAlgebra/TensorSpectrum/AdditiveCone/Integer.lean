import OAI.LinearAlgebra.TensorSpectrum.AdditiveCone.Rational
import OAI.LinearAlgebra.TensorSpectrum.AdditiveCone.Denominators
import Mathlib.Data.Rat.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Integer finite obstruction

Integer-coefficient affine inequalities inherit a nonnegative integer
infeasibility certificate from rational Fourier–Motzkin elimination.  Paired
rows encode additive relations and normalization without quotienting a real
vector space or assuming a closed-cone theorem.
-/

open scoped BigOperators

namespace OAI.LinearAlgebra.TensorSpectrum.AdditiveCone

universe u

/-- Farkas certificate with integer weights for a real-infeasible integer system. -/
theorem integer_certificate_of_no_real_solution {ι : Type u} [Fintype ι] {n : ℕ}
    (a : ι → Fin n → ℤ) (b : ι → ℤ)
    (h : ¬ ∃ x : Fin n → ℝ,
      ∀ i, 0 ≤ (∑ k, (a i k : ℝ) * x k) + (b i : ℝ)) :
    ∃ c : ι → ℤ, (∀ i, 0 ≤ c i) ∧
      (∀ k, ∑ i, c i * a i k = 0) ∧ (∑ i, c i * b i) < 0 := by
  classical
  have hq : ¬ ∃ x : Fin n → ℚ,
      ∀ i, 0 ≤ (∑ k, (a i k : ℚ) * x k) + (b i : ℚ) := by
    rintro ⟨x, hx⟩
    apply h
    refine ⟨fun k => (x k : ℝ), ?_⟩
    intro i
    change (0 : ℝ) ≤ (∑ k, (a i k : ℝ) * (x k : ℝ)) + (b i : ℝ)
    exact_mod_cast hx i
  obtain ⟨c⟩ := rational_certificate_of_infeasible
    (fun i k => (a i k : ℚ)) (fun i => (b i : ℚ)) hq
  obtain ⟨m, hm, z, hz, hzpos⟩ := exists_pos_nat_mul_eq_int c.weight
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  refine ⟨z, (fun i => hzpos i (c.nonneg i)), ?_, ?_⟩
  · intro k
    have heq : (∑ i, (z i : ℚ) * (a i k : ℚ)) = 0 := by
      simp_rw [hz]
      rw [show (∑ i, (m : ℚ) * c.weight i * (a i k : ℚ)) =
        (m : ℚ) * (∑ i, c.weight i * (a i k : ℚ)) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring]
      rw [c.cancel, mul_zero]
    exact_mod_cast heq
  · have hneg : (∑ i, (z i : ℚ) * (b i : ℚ)) < 0 := by
      simp_rw [hz]
      rw [show (∑ i, (m : ℚ) * c.weight i * (b i : ℚ)) =
        (m : ℚ) * (∑ i, c.weight i * (b i : ℚ)) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring]
      exact mul_neg_of_pos_of_neg hm' c.negative
    exact_mod_cast hneg

private abbrev NormalizedRow (ι κ : Type u) := ι ⊕ (κ ⊕ (κ ⊕ Bool))

private def normalizedCoefficients {ι κ : Type u} {n : ℕ}
    (g : ι → Fin n → ℤ) (r : κ → Fin n → ℤ) (unit : Fin n → ℤ) :
    NormalizedRow ι κ → Fin n → ℤ
  | Sum.inl i => g i
  | Sum.inr (Sum.inl j) => r j
  | Sum.inr (Sum.inr (Sum.inl j)) => fun k => -r j k
  | Sum.inr (Sum.inr (Sum.inr true)) => unit
  | Sum.inr (Sum.inr (Sum.inr false)) => fun k => -unit k

private def normalizedConstants {ι κ : Type u} : NormalizedRow ι κ → ℤ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl _)) => 0
  | Sum.inr (Sum.inr (Sum.inr true)) => -1
  | Sum.inr (Sum.inr (Sum.inr false)) => 1

/-- The finite integer cone certificate used in Appendix A.1.

Failure of a normalized real functional that kills the additive relations and
is nonnegative on the inequality vectors yields a strictly positive integer
multiple of the negative unit, with nonnegative integer cone coefficients and
unrestricted integer relation coefficients.
-/
theorem integer_cone_certificate_of_no_state
    {ι κ : Type u} [Fintype ι] [Fintype κ] {n : ℕ}
    (g : ι → Fin n → ℤ) (r : κ → Fin n → ℤ) (unit : Fin n → ℤ)
    (h : ¬ ∃ L : Fin n → ℝ,
      (∑ k, (unit k : ℝ) * L k) = 1 ∧
      (∀ i, 0 ≤ ∑ k, (g i k : ℝ) * L k) ∧
      (∀ j, (∑ k, (r j k : ℝ) * L k) = 0)) :
    ∃ m : ℤ, 0 < m ∧ ∃ c : ι → ℤ, ∃ d : κ → ℤ,
      (∀ i, 0 ≤ c i) ∧
      ∀ k, -m * unit k = (∑ i, c i * g i k) + ∑ j, d j * r j k := by
  classical
  let a := normalizedCoefficients g r unit
  let b : NormalizedRow ι κ → ℤ := normalizedConstants
  have hsys : ¬ ∃ L : Fin n → ℝ,
      ∀ i, 0 ≤ (∑ k, (a i k : ℝ) * L k) + (b i : ℝ) := by
    rintro ⟨L, hL⟩
    apply h
    refine ⟨L, ?_, ?_, ?_⟩
    · have hp := hL (Sum.inr (Sum.inr (Sum.inr true)))
      have hn := hL (Sum.inr (Sum.inr (Sum.inr false)))
      simp only [a, b, normalizedCoefficients, normalizedConstants,
        Int.cast_neg, Int.cast_one, neg_mul, Finset.sum_neg_distrib] at hp hn
      linarith
    · intro i
      have hi := hL (Sum.inl i)
      simpa only [a, b, normalizedCoefficients, normalizedConstants,
        Int.cast_zero, add_zero] using hi
    · intro j
      have hp := hL (Sum.inr (Sum.inl j))
      have hn := hL (Sum.inr (Sum.inr (Sum.inl j)))
      simp only [a, b, normalizedCoefficients, normalizedConstants,
        Int.cast_neg, Int.cast_zero, neg_mul, Finset.sum_neg_distrib, add_zero] at hp hn
      linarith
  obtain ⟨w, hwpos, hwzero, hwneg⟩ :=
    integer_certificate_of_no_real_solution a b hsys
  let α := w (Sum.inr (Sum.inr (Sum.inr true)))
  let β := w (Sum.inr (Sum.inr (Sum.inr false)))
  let c : ι → ℤ := fun i => w (Sum.inl i)
  let d : κ → ℤ := fun j =>
    w (Sum.inr (Sum.inl j)) - w (Sum.inr (Sum.inr (Sum.inl j)))
  have hm : 0 < α - β := by
    have hneg : -α + β < 0 := by
      simpa [b, normalizedConstants, Fintype.sum_sum_type, α, β] using hwneg
    linarith
  refine ⟨α - β, hm, c, d, (fun i => hwpos (Sum.inl i)), ?_⟩
  intro k
  have heq := hwzero k
  have heq' : (∑ i, c i * g i k) + (∑ j, d j * r j k) +
      (α - β) * unit k = 0 := by
    simp only [a, normalizedCoefficients, Fintype.sum_sum_type,
      Fintype.sum_bool, mul_neg, Finset.sum_neg_distrib] at heq
    simp only [d, sub_mul, Finset.sum_sub_distrib]
    dsimp [c, α, β] at *
    linarith
  linarith

end OAI.LinearAlgebra.TensorSpectrum.AdditiveCone
