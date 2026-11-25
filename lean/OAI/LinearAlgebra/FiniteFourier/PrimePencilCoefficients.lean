import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-! # Gaussian binomial coefficients at a primitive root of unity

The coefficient of an ordered monomial in a power of two quantum-commuting
variables obeys the Gaussian Pascal recurrence. A denominator-free identity
gives its vanishing in every interior position of a primitive-order row.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- Gaussian Pascal recurrence for the ordered monomials in a quantum binomial. -/
def quantumBinom {K : Type*} [Semiring K] (q : K) : ℕ → ℕ → K
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => q ^ (k + 1) * quantumBinom q n (k + 1) + quantumBinom q n k

section Semiring
variable {K : Type*} [Semiring K] (q : K)

@[simp] theorem quantumBinom_zero_right (n : ℕ) : quantumBinom q n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem quantumBinom_zero_succ (k : ℕ) : quantumBinom q 0 (k + 1) = 0 := rfl

theorem quantumBinom_succ_succ (n k : ℕ) : quantumBinom q (n + 1) (k + 1) =
    q ^ (k + 1) * quantumBinom q n (k + 1) + quantumBinom q n k := rfl

theorem quantumBinom_eq_zero_of_lt {n k : ℕ} (hk : n < k) : quantumBinom q n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp_all
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp [quantumBinom_succ_succ, ih (show n < k + 1 by omega), ih (show n < k by omega)]

@[simp] theorem quantumBinom_self (n : ℕ) : quantumBinom q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [quantumBinom_succ_succ, quantumBinom_eq_zero_of_lt q (Nat.lt_succ_self n), ih]

end Semiring

section CommRing
variable {K : Type*} [CommRing K] (q : K)

/-- Ratio between adjacent Gaussian coefficients without division. -/
theorem quantumBinom_ratio (n k : ℕ) (hk : k ≤ n) :
    (q ^ (k + 1) - 1) * quantumBinom q n (k + 1) =
      (q ^ (n - k) - 1) * quantumBinom q n k := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    by_cases he : k = n + 1
    · subst k
      simp [quantumBinom_eq_zero_of_lt q (Nat.lt_succ_self (n + 1))]
    have hkn : k ≤ n := by omega
    cases k with
    | zero =>
      have h := ih 0 (Nat.zero_le n)
      simp only [zero_add, pow_one, Nat.sub_zero, quantumBinom_zero_right, mul_one] at h ⊢
      rw [quantumBinom_succ_succ, pow_one, quantumBinom_zero_right, pow_succ]
      linear_combination q * h
    | succ k =>
      have hl := ih (k + 1) hkn
      have hr := ih k (by omega)
      have hpow₁ : q ^ (k + 2) * q ^ (n - (k + 1)) = q ^ (n + 1) := by
        rw [← pow_add]
        congr 1
        omega
      have hpow₂ : q ^ (k + 1) * q ^ (n - k) = q ^ (n + 1) := by
        rw [← pow_add]
        congr 1
        omega
      simp only [quantumBinom_succ_succ, Nat.succ_sub_succ_eq_sub]
      linear_combination q ^ (k + 2) * hl + hr +
        (hpow₁ - hpow₂) * quantumBinom q n (k + 1)

/-- The equivalent Gaussian Pascal recurrence with the power on the lower-index term. -/
theorem quantumBinom_succ_succ' (n k : ℕ) (hk : k ≤ n) :
    quantumBinom q (n + 1) (k + 1) =
      quantumBinom q n (k + 1) + q ^ (n - k) * quantumBinom q n k := by
  rw [quantumBinom_succ_succ]
  linear_combination quantumBinom_ratio q n k hk

/-- Consecutive rows of the Gaussian binomial triangle satisfy a denominator-free identity. -/
theorem quantumBinom_mul_pred (n k : ℕ) (hk : k ≤ n) :
    (q ^ (k + 1) - 1) * quantumBinom q (n + 1) (k + 1) =
      (q ^ (n + 1) - 1) * quantumBinom q n k := by
  have hp : q ^ (k + 1) * q ^ (n - k) = q ^ (n + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [quantumBinom_succ_succ]
  linear_combination q ^ (k + 1) * quantumBinom_ratio q n k hk + hp * quantumBinom q n k

/-- Every interior coefficient in the row indexed by the order of a primitive root vanishes. -/
theorem quantumBinom_eq_zero_of_primitiveRoot [IsDomain K] {b k : ℕ}
    {q : K} (hq : IsPrimitiveRoot q b) (hk : 0 < k) (hkb : k < b) :
    quantumBinom q b k = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  have h := quantumBinom_mul_pred q b k (by omega)
  rw [hq.pow_eq_one, sub_self, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (hq.pow_ne_one_of_pos_of_lt hk.ne' hkb))

end CommRing

end FiniteFourier
end LinearAlgebra
end OAI
