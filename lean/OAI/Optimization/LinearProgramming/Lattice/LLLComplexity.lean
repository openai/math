import OAI.Optimization.LinearProgramming.Lattice.LLLIndependence
import Mathlib.Data.Nat.Size

/-! Initial sizes and the swap count in the Gram-determinant potential argument of Appendix A. -/

open Finset Matrix
open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

/-- Absolute Gram determinant on the first `k` rows. -/
def prefixGramMagnitude {p n : ℕ} (A : Matrix (Fin p) (Fin n) ℤ) (k : Fin (p + 1)) : ℕ :=
  let rows := A.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) id
  (rows * rows.transpose).det.natAbs

/-- The potential used for the swap bound, including all nonempty row prefixes. -/
def reductionPotential {p n : ℕ} (A : Matrix (Fin p) (Fin n) ℤ) : ℕ :=
  ∏ k : Fin p, prefixGramMagnitude A k.succ

/-- Polynomial binary length for every input prefix Gram determinant. -/
theorem prefixGramMagnitude_le {p n L : ℕ} (A : Matrix (Fin p) (Fin n) ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ L) (k : Fin (p + 1)) :
    prefixGramMagnitude A k ≤ 2 ^ ((p + n + 2 * L) * p) := by
  let rows := A.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) id
  have hrows : ∀ i j, (rows i j).natAbs ≤ 2 ^ L := fun i j => hA _ _
  have hk : (k : ℕ) ≤ p := Nat.le_of_lt_succ k.isLt
  have hp2 : (k : ℕ) ≤ 2 ^ p := hk.trans (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hn2 : n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    prefixGramMagnitude A k ≤ k.val.factorial * (n * (2 ^ L * 2 ^ L)) ^ k.val :=
      by simpa only [prefixGramMagnitude, pow_two] using gram_det_bound rows hrows
    _ ≤ (2 ^ p) ^ k.val * (2 ^ n * (2 ^ L * 2 ^ L)) ^ k.val :=
      Nat.mul_le_mul (k.val.factorial_le_pow.trans (Nat.pow_le_pow_left hp2 k.val))
        (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hn2) k.val)
    _ = 2 ^ ((p + n + 2 * L) * k.val) := by
      rw [← mul_pow, ← pow_add, ← pow_add, ← pow_add, ← pow_mul]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hk)

/-- Initial potential has at most `1 + (p+n+2L)p²` bits. -/
theorem reductionPotential_size_le {p n L : ℕ} (A : Matrix (Fin p) (Fin n) ℤ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ L) :
    (reductionPotential A).size ≤ (p + n + 2 * L) * p * p + 1 := by
  have hpot : reductionPotential A ≤ 2 ^ ((p + n + 2 * L) * p * p) := by
    calc
      _ ≤ ∏ _i : Fin p, 2 ^ ((p + n + 2 * L) * p) :=
        Finset.prod_le_prod fun i _ => prefixGramMagnitude_le A hA i.succ
      _ = _ := by simp [pow_mul]
  simpa only [Nat.size_pow] using Nat.size_le_size hpot

/-- Three successive LLL swaps at factor `3/4` cut the potential by more than half.
Consequently a sequence of swaps has length strictly less than three times its initial bit length. -/
theorem swap_count_lt_three_mul_size {P : ℕ → ℕ} {t : ℕ}
    (hpos : ∀ i ≤ t, 0 < P i) (hdrop : ∀ i < t, 4 * P (i+1) ≤ 3 * P i) :
    t < 3 * (P 0).size := by
  have block (j : ℕ) (hj : 3 * j ≤ t) : 2 ^ j * P (3 * j) ≤ P 0 := by
    induction j with
    | zero => simp
    | succ j ih =>
      have hj' : 3 * j + 3 ≤ t := by omega
      have h0 := hdrop (3*j) (by omega)
      have h1 := hdrop (3*j+1) (by omega)
      have h2 := hdrop (3*j+2) (by omega)
      have half : 2 * P (3*j+3) ≤ P (3*j) := by
        change 4 * P (3*j+2) ≤ 3 * P (3*j+1) at h1
        change 4 * P (3*j+3) ≤ 3 * P (3*j+2) at h2
        omega
      rw [Nat.mul_succ, pow_succ, Nat.mul_assoc]
      exact (Nat.mul_le_mul_left _ half).trans (ih (by omega))
  by_contra! ht
  have hP := block (P 0).size ht
  have hlast := hpos _ ht
  have hsmall := Nat.lt_size_self (P 0)
  have := Nat.mul_le_mul_left (2^(P 0).size) hlast
  omega

end Lattice
end LinearProgramming
end Optimization
end OAI
