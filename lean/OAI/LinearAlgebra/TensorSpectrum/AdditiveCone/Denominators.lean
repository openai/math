import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Clearing denominators in finite rational cones

A single positive natural number clears every denominator of a finite rational
coefficient vector. The resulting integer vector preserves nonnegativity. The
last two lemmas transport finite linear identities through this construction.
-/

namespace OAI.LinearAlgebra.TensorSpectrum.AdditiveCone

open scoped BigOperators

/-- A common positive denominator for a finite rational vector, with signs
preserved coordinatewise. The product construction includes the empty type. -/
theorem exists_pos_nat_mul_eq_int {ι : Type*} [Fintype ι] (c : ι → ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∃ z : ι → ℤ,
      (∀ i, (z i : ℚ) = (m : ℚ) * c i) ∧
      (∀ i, 0 ≤ c i → 0 ≤ z i) := by
  classical
  let m : ℕ := ∏ i, (c i).den
  let z : ι → ℤ := fun i =>
    (∏ j ∈ Finset.univ.erase i, (c j).den : ℕ) * (c i).num
  have hm : 0 < m := Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (c i).den_pos.ne')
  refine ⟨m, hm, z, ?_, ?_⟩
  · intro i
    have hprod : m = (∏ j ∈ Finset.univ.erase i, (c j).den) * (c i).den :=
      (Finset.prod_erase_mul Finset.univ (fun j => (c j).den)
        (Finset.mem_univ i)).symm
    dsimp only [z]
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [hprod, Nat.cast_mul, mul_assoc, Rat.den_mul_eq_num]
  · intro i hi
    exact Int.mul_nonneg (Int.natCast_nonneg _) (Rat.num_nonneg.mpr hi)

/-- A nonnegative rational coefficient vector has a positive integral scaling
which is a nonnegative integer coefficient vector. -/
theorem exists_nonneg_int_scaling {ι : Type*} [Fintype ι]
    (c : ι → ℚ) (hc : ∀ i, 0 ≤ c i) :
    ∃ m : ℕ, 0 < m ∧ ∃ z : ι → ℤ,
      (∀ i, 0 ≤ z i) ∧ (∀ i, (z i : ℚ) = (m : ℚ) * c i) := by
  obtain ⟨m, hm, z, hz, hnonneg⟩ := exists_pos_nat_mul_eq_int c
  exact ⟨m, hm, z, fun i => hnonneg i (hc i), hz⟩

/-- Scaling rational coefficients scales each finite integer linear form. -/
theorem cast_sum_mul_of_cleared {ι : Type*} [Fintype ι]
    {c : ι → ℚ} {z : ι → ℤ} {m : ℕ}
    (hz : ∀ i, (z i : ℚ) = (m : ℚ) * c i) (v : ι → ℤ) :
    ((∑ i, z i * v i : ℤ) : ℚ) = (m : ℚ) * ∑ i, c i * (v i : ℚ) := by
  rw [Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Int.cast_mul, hz i, mul_assoc]

/-- A rational linear identity becomes an integer linear identity once its
coefficients have been cleared. -/
theorem sum_mul_eq_nat_mul_of_cleared {ι : Type*} [Fintype ι]
    {c : ι → ℚ} {z : ι → ℤ} {m : ℕ}
    (hz : ∀ i, (z i : ℚ) = (m : ℚ) * c i) (v : ι → ℤ) (b : ℤ)
    (h : ∑ i, c i * (v i : ℚ) = (b : ℚ)) :
    ∑ i, z i * v i = (m : ℤ) * b := by
  apply Rat.intCast_injective
  rw [cast_sum_mul_of_cleared hz v, h, Int.cast_mul, Int.cast_natCast]

end OAI.LinearAlgebra.TensorSpectrum.AdditiveCone
