import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionFactor
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickClear

/-! # Coefficients of the clearing polynomial

The signed binomial multiplier of the fermionic coefficient identity is the
finite-difference stencil for multiplication by a power of `1 - T 1`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Finset LaurentPolynomial

private theorem multiplier_succ_succ (L a : ℕ) :
    multiplier (L+1) (a+1) = multiplier L (a+1) - multiplier L a := by
  simp only [multiplier, pow_succ, Nat.choose_succ_succ, Nat.cast_add]
  ring

/-- The binomial multiplier gives the coefficients of the iterated backward difference. -/
theorem iterate_kernelDifference_eq_sum (f : ℤ → ℤ) (L : ℕ) (s : ℤ) :
    (kernelDifference^[L] f) s = ∑ a ∈ range (L+1), multiplier L a * f (s-a) := by
  induction L generalizing s with
  | zero => simp [multiplier]
  | succ L ih =>
    rw [Function.iterate_succ_apply', kernelDifference, ih, ih, sum_range_succ' (n := L+1)]
    simp_rw [multiplier_succ_succ, sub_mul]
    rw [sum_sub_distrib]
    have hsum : (∑ a ∈ range (L+1), multiplier L (a+1) * f (s-(a+1 : ℕ))) +
        multiplier L 0 * f (s-(0 : ℕ)) = ∑ a ∈ range (L+1), multiplier L a * f (s-a) := by
      rw [← sum_range_succ' (fun a ↦ multiplier L a * f (s-a))]
      rw [sum_range_succ]
      simp [multiplier]
    have hshift (a : ℕ) : s-(a+1 : ℕ) = s-1-a := by push_cast; ring
    simp only [hshift] at *
    simp only [multiplier, pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
      Nat.cast_zero, sub_zero] at *
    omega

/-- Padding the multiplier sum with zero coefficients gives the finite index
used in the integral coefficient identity. -/
theorem iterate_kernelDifference_eq_fin_sum (f : ℤ → ℤ) {L H : ℕ} (h : L ≤ H) (s : ℤ) :
    (kernelDifference^[L] f) s = ∑ a : Fin (H+1), multiplier L a * f (s-a) := by
  rw [iterate_kernelDifference_eq_sum, Fin.sum_univ_eq_sum_range (fun a : ℕ ↦ multiplier L a * f (s-a))]
  apply sum_subset_zero_on_sdiff (Finset.range_mono (by omega))
  · intro a ha
    have hla : L < a := by simpa using (mem_sdiff.mp ha).2
    simp [multiplier, Nat.choose_eq_zero_of_lt hla]
  · intro _ _
    rfl

/-- Extract the signed binomial convolution from a cleared Laurent coefficient. -/
theorem coeff_clear_pow_multiplier (f : LaurentPolynomial ℤ) (L : ℕ) (s : ℤ) :
    ((1 - T 1)^L * f).coeff s = ∑ a ∈ range (L+1), multiplier L a * f.coeff (s-a) := by
  rw [coeff_clear_pow, iterate_kernelDifference_eq_sum]

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
