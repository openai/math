import OAI.LinearAlgebra.SpectralBooks.Fermion.WickContraction
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickKernel

/-! # Reverse Laurent expansion of a truncated contraction

For the reversed pair the first possible mode is `i`, and its translate by
`t` contributes at Laurent degree `-t-i-j-1`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion
open LaurentPolynomial

private theorem reverse_kernelNumerator (i j : ℕ) :
    -kernelNumerator j i = (-1) ^ (i + j + 1) * kernelNumerator i j := by
  have hsign : (-1 : ℤ)^i * (-1)^i = 1 := by rw [← mul_pow]; simp
  unfold kernelNumerator
  rw [add_comm j i, ← Nat.choose_symm_add (a := i) (b := j), pow_succ, pow_add]
  linear_combination ((-1 : ℤ)^j * ((i+j).choose i : ℤ)) * hsign

private theorem reverse_contraction_mode (i j t : ℕ) :
    -(annihilationCoeff (true,j) (i+t) * creationCoeff (false,i) (i+t)) =
      C (((-1) ^ (i+j+1) : ℤ) * kernelNumerator i j * forwardKernel (i+j+1) (t : ℤ)) *
        T (-(t : ℤ) - i - j - 1) := by
  have hd := differentiated_kernel (i+t) j i
  rw [Nat.cast_add, add_sub_cancel_left, add_comm j i] at hd
  simp only [annihilationCoeff, creationCoeff, fieldExponent, ite_true, Bool.false_eq_true, ite_false,
    T_zero, mul_one, Nat.cast_add]
  rw [mul_right_comm (C _) (T _) (C _), ← map_mul, ← neg_mul, ← map_neg, hd, ← neg_mul,
    reverse_kernelNumerator]
  congr 2
  ring

/-- The negative truncated contraction of a reversed field pair, as a Laurent
polynomial in the second variable. -/
theorem neg_contractionPolynomial_reverse (N i j : ℕ) :
    -contractionPolynomial N (true,j) (false,i) =
      ∑ t ∈ Finset.range (N-i),
        C (((-1)^(i+j+1) : ℤ) * kernelNumerator i j * forwardKernel (i+j+1) (t:ℤ)) *
          T (-(t:ℤ)-i-j-1) := by
  unfold contractionPolynomial
  rw [Fin.sum_univ_eq_sum_range (fun r ↦ annihilationCoeff (true,j) r * creationCoeff (false,i) r),
    ← Finset.sum_neg_distrib]
  have hvanish (n : ℕ) (hn : n ≤ i) :
      ∑ r ∈ Finset.range n, -(annihilationCoeff (true,j) r * creationCoeff (false,i) r) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp [creationCoeff, Nat.choose_eq_zero_of_lt ((Finset.mem_range.mp hr).trans_le hn)]
  rcases le_total N i with hN | hN
  · rw [hvanish N hN, Nat.sub_eq_zero_of_le hN]
    simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [Finset.sum_range_add, hvanish i le_rfl, zero_add, Nat.add_sub_cancel_left]
    exact Finset.sum_congr rfl fun t _ ↦ reverse_contraction_mode i j t

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
