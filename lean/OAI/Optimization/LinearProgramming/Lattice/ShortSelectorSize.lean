import OAI.Optimization.LinearProgramming.Lattice.DyadicEntrySize
import OAI.Optimization.LinearProgramming.Lattice.ShortSelectorCore
import OAI.Optimization.LinearProgramming.Lattice.QuerySize
import OAI.Optimization.LinearProgramming.Lattice.LLLRational

/-! Encoded sizes of the explicit rational graph-lattice inputs to LLL. -/

open scoped Rat

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

/-- Every output of the normalized ratio bisection has a small reduced numerator and denominator,
even if the sign oracle gave inconsistent comparisons. -/
theorem normalizedRowApprox_size {n p : ℕ} (oracle : (Fin p → ℤ) → Bool)
    (P : Fin n → Fin p → ℚ) (k : ℕ) (i : Fin n) :
    (normalizedRowApprox oracle P k i).num.natAbs.size ≤ k + 1 ∧
      (normalizedRowApprox oracle P k i).den.size ≤ k + 1 := by
  unfold normalizedRowApprox
  split
  · simp
  · exact dyadic_entry_size _ k (dyadicSearch_numerator_lt ..).le

/-- Every entry of the rational matrix passed to LLL has at most `searchPrecision p M + 1`
bits in each of its reduced numerator and denominator. -/
theorem shortSelector_input_size {p : ℕ} (M : ℕ) (u : Fin p → ℚ)
    (hu : ∀ i, (u i).num.natAbs.size ≤ searchPrecision p M + 1 ∧ (u i).den.size ≤ searchPrecision p M + 1)
    (i j : Fin (p+1)) :
    let A := rationalGraphMatrix (1 / (searchDenominator p M : ℚ)^(p+1)) u
    (A i j).num.natAbs.size ≤ searchPrecision p M + 1 ∧ (A i j).den.size ≤ searchPrecision p M + 1 := by
  let e := precisionExponent p M * (p+1)
  have he : (searchDenominator p M : ℚ)^(p+1) = (2 : ℚ)^e := by simp [e, searchDenominator, pow_mul]
  have hle : e ≤ searchPrecision p M := Nat.mul_le_mul_left _ (by omega)
  have h1 : |(1 : ℤ)| ≤ (2 : ℤ)^e := by simp; exact one_le_pow₀ (by decide)
  have hα := dyadic_entry_size 1 e h1
  change (rationalGraphMatrix _ u i j).num.natAbs.size ≤ _ ∧ _
  refine Fin.cases ?_ (fun t ↦ ?_) i <;> refine Fin.cases ?_ (fun s ↦ ?_) j
  · simp only [rationalGraphMatrix, Fin.cons_zero, he]
    exact ⟨hα.1.trans (Nat.add_le_add_right hle 1), hα.2.trans (Nat.add_le_add_right hle 1)⟩
  · exact hu s
  · simp [rationalGraphMatrix]
  · simp only [rationalGraphMatrix, Fin.cons_succ]
    split <;> simp

/-- Assembling the integer graph matrix for a real-input oracle call stays within an explicit
polynomial bit bound, including the common denominator used before reduction. -/
theorem shortSelector_cleared_input_size {p n : ℕ} (M : ℕ) (oracle : (Fin n → ℤ) → Bool)
    (P : Fin p → Fin n → ℚ) (i j : Fin (p+1)) :
    let u := normalizedRowApprox oracle P (searchPrecision p M)
    let A := rationalGraphMatrix (1 / (searchDenominator p M : ℚ)^(p+1)) u
    (integralRows A i j).natAbs.size ≤ (searchPrecision p M + 1) * ((p+1)*(p+1) + 1) :=
  integralRows_natAbs_size _ (shortSelector_input_size M _ (normalizedRowApprox_size oracle P _)) i j

/-- Integer row operations preserve the input common denominator; this includes every coordinate
of a reduced graph-lattice row, even before the output is decoded. -/
theorem rowLattice_denominator_dvd {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℚ) {r : Fin p → ℚ}
    (hr : r ∈ Submodule.span ℤ (Set.range A)) (i : Fin p) : (r i).den ∣ matrixDenominator A := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hr
  have hi : r i = ∑ j, (a j : ℚ) * A j i := by
    rw [← ha, Finset.sum_apply]; simp [zsmul_eq_mul]
  let c := ∑ j, a j * integralRows A j i
  have hd : ((matrixDenominator A : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (matrixDenominator_pos A).ne'
  have hrepr : r i = (c : ℚ) / (matrixDenominator A : ℤ) := by
    apply (eq_div_iff hd).mpr
    rw [hi, mul_comm]
    exact (integralRows_combination A a i).symm
  have hZ : ((r i).den : ℤ) ∣ (matrixDenominator A : ℤ) := by
    rw [hrepr, Rat.intCast_div_eq_divInt]
    exact Rat.den_dvd ..
  exact_mod_cast hZ

/-- Any graph lattice vector whose norm is at most one has polynomial-bit input to the
first-row decoder. The bound uses the dimensions and the input-entry denominator lengths. -/
theorem small_rowLattice_entry_size {n p L : ℕ} (A : Matrix (Fin n) (Fin p) ℚ)
    (hd : ∀ k t, (A k t).den.size ≤ L) {r : Fin p → ℚ} (hr : r ∈ Submodule.span ℤ (Set.range A))
    (i : Fin p) (hi : |r i| ≤ 1) :
    (r i).num.natAbs.size ≤ L*(n*p) + 1 ∧ (r i).den.size ≤ L*(n*p) + 1 := by
  have hden := Nat.le_of_dvd (matrixDenominator_pos A) (rowLattice_denominator_dvd A hr i)
  have hD := matrixDenominator_le_pow A (2^L) (fun k t ↦ (Nat.size_le.mp (hd k t)).le)
  rw [← pow_mul] at hD
  have h := Nat.size_le_size (hden.trans hD)
  rw [Nat.size_pow] at h
  have hp : (0 : ℚ) < (r i).den := by exact_mod_cast (r i).den_pos
  rw [← Rat.num_div_den (r i), abs_div, abs_of_pos hp, div_le_one hp] at hi
  have hz : |(r i).num| ≤ ((r i).den : ℤ) := by exact_mod_cast hi
  rw [Int.abs_eq_natAbs] at hz
  have hn : (r i).num.natAbs ≤ (r i).den := by exact_mod_cast hz
  exact ⟨(Nat.size_le_size hn).trans h, h⟩

end Lattice
end LinearProgramming
end Optimization
end OAI
