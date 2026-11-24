import Mathlib.NumberTheory.Chebyshev

/-!
# A small characteristic preserving a nonzero integer minor

Section 8.2 of *VP and VNP differ over every field* needs a prime avoiding a
nonzero integer determinant. If the determinant has absolute value at most
`2 ^ B`, the prime may be taken at most `2 * (B + 2) ^ 2`. The elementary
estimate for the least common multiple of the first `n` integers gives this
polynomial bound directly.
-/

namespace OAI
namespace Computability
namespace VPVNP

/-- A positive integer of at most `B + 1` binary digits has a nondividing
prime bounded quadratically in `B`. -/
theorem exists_small_prime_not_dvd {D B : ℕ} (hD : D ≠ 0) (hB : D ≤ 2 ^ B) :
    ∃ p : ℕ, p.Prime ∧ p ≤ 2 * (B + 2) ^ 2 ∧ ¬ p ∣ D := by
  let n := 2 * (B + 2) ^ 2
  let k := 2 * (B + 2)
  have hn : n ≠ 0 := by dsimp [n]; positivity
  have hsize : n + 1 ≤ 2 ^ k := Nat.two_mul_sq_add_one_le_two_pow_two_mul _
  by_contra! hall
  have hlcm : Nat.lcmUpto n ∣ D ^ k := by
    apply (Nat.factorization_prime_le_iff_dvd (Nat.lcmUpto_ne_zero n) (pow_ne_zero _ hD)).mp
    intro p hp
    rw [Nat.factorization_lcmUpto n hp, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    by_cases hpn : p ≤ n
    · have he : p.log n ≤ k := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp <|
        (Nat.pow_le_pow_left hp.two_le _).trans ((Nat.pow_log_le_self p hn).trans (by omega))
      have hpos := hp.factorization_pos_of_dvd hD (hall p hp hpn)
      exact he.trans (Nat.le_mul_of_pos_right _ hpos)
    · simp [Nat.log_of_lt (by omega : n < p)]
  have hbound : 2 ^ n ≤ 2 ^ (k + B * k) := calc
    2 ^ n ≤ (n + 1) * Nat.lcmUpto n := Chebyshev.two_pow_le_mul_lcmUpto n
    _ ≤ 2 ^ k * (2 ^ B) ^ k := Nat.mul_le_mul hsize
      ((Nat.le_of_dvd (Nat.pow_pos (Nat.pos_of_ne_zero hD)) hlcm).trans (Nat.pow_le_pow_left hB _))
    _ = _ := by rw [pow_add, pow_mul (2 : ℕ) B k]
  have := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound
  dsimp [n, k] at this
  nlinarith

/-- The integer minor stays nonzero modulo a prime with the same bound. -/
theorem exists_small_prime_not_dvd_int {D : ℤ} {B : ℕ} (hD : D ≠ 0) (hB : D.natAbs ≤ 2 ^ B) :
    ∃ p : ℕ, p.Prime ∧ p ≤ 2 * (B + 2) ^ 2 ∧ ¬ (p : ℤ) ∣ D := by
  obtain ⟨p, hp, hbound, hn⟩ := exists_small_prime_not_dvd (Int.natAbs_ne_zero.mpr hD) hB
  exact ⟨p, hp, hbound, fun h ↦ hn (by simpa using (Int.natAbs_dvd_natAbs.mpr h))⟩

end VPVNP
end Computability
end OAI
