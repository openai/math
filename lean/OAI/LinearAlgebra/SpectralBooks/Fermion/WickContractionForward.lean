import OAI.LinearAlgebra.SpectralBooks.Fermion.WickContraction
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickKernel

/-! # The forward finite contraction kernel

Only modes `r ≥ j` contribute to the contraction of a field at one with
a field at `X`. Reindexing by `t = r - j` yields the truncation of the
forward power series at degree `N - j` (exclusive).
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open LaurentPolynomial Finset
noncomputable section

/-- The contraction at `(1, X)` is the truncated Taylor expansion of the kernel. -/
theorem contractionPolynomial_forward (N i j : ℕ) :
    contractionPolynomial N (false, i) (true, j) =
      ∑ t ∈ range (N - j), C (kernelNumerator i j * forwardKernel (i + j + 1) (t : ℤ)) *
        T (t : ℤ) := by
  rw [contractionPolynomial, Fin.sum_univ_eq_sum_range
    (fun r ↦ annihilationCoeff (false, i) r * creationCoeff (true, j) r)]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    by_cases hj : j ≤ N
    · rw [show N + 1 - j = (N - j) + 1 by omega, sum_range_succ]
      congr 1
      simp only [annihilationCoeff, creationCoeff, fieldExponent, Bool.false_eq_true, ite_false,
        ite_true, T_zero, mul_one, Nat.cast_sub hj, ← mul_assoc, ← map_mul, differentiated_kernel]
    · have h₀ : N.choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [show N + 1 - j = 0 by omega, show N - j = 0 by omega, creationCoeff, h₀]

end
end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
