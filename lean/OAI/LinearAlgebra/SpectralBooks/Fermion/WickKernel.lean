import OAI.LinearAlgebra.SpectralBooks.Fermion.WickModes
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! # Integral expansions of the fermionic contraction kernel

After setting `z = 1` and `w = X`, the creation-deletion contraction
is the expansion of a power of `(1-X)⁻¹`. Forward and reversed products
expand at zero and infinity respectively. Multiplication by `1-X` is the
backward difference of their integer-indexed coefficient sequences.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion
open PowerSeries
open scoped PowerSeries

/-- Numerator from differentiating the two ends of the propagator. -/
def kernelNumerator (i j : ℕ) : ℤ := (-1)^i * ((i+j).choose i : ℤ)

/-- The forward expansion of `(1-X)^(-k)`, extended by zero at negative degrees. -/
def forwardKernel (k : ℕ) : ℤ → ℤ
  | .ofNat n => coeff n (invOneSubPow ℤ k).val
  | .negSucc _ => 0

/-- The expansion at infinity of the same rational function. -/
def reverseKernel (k : ℕ) (s : ℤ) : ℤ := (-1)^k * forwardKernel k (-s-k)

theorem forwardKernel_succ_nat (k n : ℕ) :
    forwardKernel (k+1) n = ((k+n).choose k : ℤ) := by
  simp [forwardKernel, invOneSubPow_val_succ_eq_mk_add_choose]

/-- The differentiated scalar from contracting a mode `r` of the first
field with the matching mode of the second field. -/
theorem differentiated_kernel (r i j : ℕ) :
    negativeChoose r i * (r.choose j : ℤ) =
      kernelNumerator i j * forwardKernel (i+j+1) ((r : ℤ)-j) := by
  by_cases h : j ≤ r
  · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.cast_add, add_sub_cancel_left, forwardKernel_succ_nat]
    have hn := Nat.choose_mul (n := i+j+t) (k := i+j) (s := i) (by omega)
    have hsub : i+j+t-i = j+t := by omega
    rw [hsub, Nat.add_sub_cancel_left] at hn
    have hn' : ((j+t+i).choose i : ℤ) * (j+t).choose j =
        ((i+j).choose i : ℤ) * (i+j+t).choose (i+j) := by
      exact_mod_cast (by simpa [add_assoc, add_comm, add_left_comm, mul_comm] using hn.symm :
        (j+t+i).choose i * (j+t).choose j = (i+j).choose i * (i+j+t).choose (i+j))
    simpa only [negativeChoose, kernelNumerator, mul_assoc] using congrArg ((-1:ℤ)^i * ·) hn'
  · rw [Nat.choose_eq_zero_of_lt (by omega : r < j)]
    have he : (r : ℤ)-j = .negSucc (j-r-1) := by omega
    simp [he, forwardKernel]

/-- On coefficient sequences this is multiplication by `1-X`. -/
def kernelDifference (f : ℤ → ℤ) (s : ℤ) := f s - f (s-1)

private theorem annihilate (k : ℕ) : (1 - (X : ℤ⟦X⟧)) * (invOneSubPow ℤ (k+1)).val =
    (invOneSubPow ℤ k).val := by
  simpa using one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℤ k 1

theorem difference_forwardKernel (k : ℕ) :
    kernelDifference (forwardKernel (k+1)) = forwardKernel k := by
  funext s
  cases s with
  | negSucc n =>
    have he : Int.negSucc n - 1 = .negSucc (n+1) := by omega
    simp [kernelDifference, forwardKernel, he]
  | ofNat n =>
    have h := congrArg (coeff n) (annihilate k)
    cases n with
    | zero =>
      change coeff 0 (invOneSubPow ℤ (k+1)).val - 0 = coeff 0 (invOneSubPow ℤ k).val
      simpa [sub_mul] using h
    | succ n =>
      unfold kernelDifference
      rw [show Int.ofNat (n+1) - 1 = Int.ofNat n by simp [Int.ofNat_eq_natCast]]
      change coeff (n+1) (invOneSubPow ℤ (k+1)).val - coeff n (invOneSubPow ℤ (k+1)).val =
        coeff (n+1) (invOneSubPow ℤ k).val
      simpa [sub_mul] using h

theorem difference_reverseKernel (k : ℕ) :
    kernelDifference (reverseKernel (k+1)) = reverseKernel k := by
  funext s
  have h := congrFun (difference_forwardKernel k) (-s-k)
  unfold kernelDifference at h
  simp only [kernelDifference, reverseKernel, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [show -s - ((k : ℤ)+1) = -s-k-1 by ring,
    show -(s-1) - ((k : ℤ)+1) = -s-k by ring, ← h]
  ring

private theorem iterate_forwardKernel (n k : ℕ) :
    kernelDifference^[n] (forwardKernel (k+n)) = forwardKernel k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change kernelDifference^[n] (kernelDifference (forwardKernel ((k+n)+1))) = _
    rw [difference_forwardKernel, ih]

private theorem iterate_reverseKernel (n k : ℕ) :
    kernelDifference^[n] (reverseKernel (k+n)) = reverseKernel k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change kernelDifference^[n] (kernelDifference (reverseKernel ((k+n)+1))) = _
    rw [difference_reverseKernel, ih]

theorem kernel_zero_equal : forwardKernel 0 = reverseKernel 0 := by
  funext s
  unfold reverseKernel
  simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
  rcases s with (_ | n) | n
  · rfl
  · rw [show -Int.ofNat (n+1) = Int.negSucc n by simp [Int.ofNat_eq_natCast, Int.negSucc_eq]]
    simp [forwardKernel, invOneSubPow_zero]
  · rw [show -Int.negSucc n = Int.ofNat (n+1) by simp [Int.ofNat_eq_natCast, Int.negSucc_eq]]
    simp [forwardKernel, invOneSubPow_zero]

/-- Clearing all poles gives identical coefficients in the two expansions. -/
theorem kernel_partial_cancellation (L k : ℕ) (h : k ≤ L) :
    kernelDifference^[L] (forwardKernel k) = kernelDifference^[L] (reverseKernel k) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm k n, Function.iterate_add_apply, Function.iterate_add_apply]
  rw [show kernelDifference^[k] (forwardKernel k) = forwardKernel 0 by
        simpa using iterate_forwardKernel k 0,
      show kernelDifference^[k] (reverseKernel k) = reverseKernel 0 by
        simpa using iterate_reverseKernel k 0, kernel_zero_equal]

/-- Leaving one pole produces the formal delta distribution. Every integer
degree has coefficient one. -/
theorem kernel_full_delta (L : ℕ) (s : ℤ) :
    (kernelDifference^[L] (forwardKernel (L+1))) s -
      (kernelDifference^[L] (reverseKernel (L+1))) s = 1 := by
  rw [add_comm L 1, iterate_forwardKernel, iterate_reverseKernel]
  rcases s with n | n
  · rw [reverseKernel, show -Int.ofNat n - (↑(1:ℕ) : ℤ) = Int.negSucc n by simp [Int.ofNat_eq_natCast, Int.negSucc_eq]; omega]
    simp [forwardKernel, invOneSubPow]
  · rw [reverseKernel, show -Int.negSucc n - (↑(1:ℕ) : ℤ) = Int.ofNat n by simp [Int.ofNat_eq_natCast, Int.negSucc_eq]]
    simp [forwardKernel, invOneSubPow]

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
