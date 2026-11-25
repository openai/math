import OAI.LinearAlgebra.FiniteFourier.PrimeClockShift
import OAI.LinearAlgebra.FiniteFourier.PrimeCyclotomicExtension

/-! # Clock pencils over prime-power root extensions

In a finite free coefficient algebra the ring may have zero divisors.
The differences of powers of the new root are units, which suffices for
both Fourier orthogonality and cancellation in the Gaussian binomial identity.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R : Type*} [CommRing R] {ξ : R} {b : ℕ}

/-- Orthogonality for a nontrivial power of a root whose powers have unit differences. -/
theorem geom_sum_primeRoot_of_units (hpow : ξ ^ b = 1)
    (hunit : ∀ k, 0 < k → k < b → IsUnit (ξ ^ k - 1)) {k : ℕ} (hk : 0 < k) (hlt : k < b) :
    ∑ i ∈ Finset.range b, (ξ ^ k) ^ i = 0 := by
  apply (hunit k hk hlt).mul_left_inj.mp
  rw [zero_mul, geom_sum_mul, ← pow_mul, Nat.mul_comm k b, pow_mul, hpow, one_pow, sub_self]

/-- The Gaussian coefficients vanish in the interior even when the coefficient
ring has zero divisors, provided the differences of powers are units. -/
theorem quantumBinom_eq_zero_of_units (hpow : ξ ^ b = 1)
    (hunit : ∀ k, 0 < k → k < b → IsUnit (ξ ^ k - 1)) {k : ℕ} (hk : 0 < k) (hlt : k < b) :
    quantumBinom ξ b k = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  apply (hunit _ hk hlt).mul_right_inj.mp
  simpa only [hpow, sub_self, zero_mul, mul_zero] using quantumBinom_mul_pred ξ n k (by omega)

/-- The affine clock pencil over any coefficient ring carrying these roots. -/
theorem qClock_sum_pow_of_units [NeZero b] {h : ℕ} (hpow : ξ ^ b = 1)
    (hunit : ∀ k, 0 < k → k < b → IsUnit (ξ ^ k - 1)) (factors : Fin h → Fin b → R) :
    (∑ i, qClockTerm ξ factors i) ^ b =
      (∑ i, ∏ t, factors i t) • (1 : Matrix (Fin h → Fin b) (Fin h → Fin b) R) := by
  rw [potter_fin_sum_of_vanishing (NeZero.pos b) (fun _ => quantumBinom_eq_zero_of_units hpow hunit)
    _ (fun i j hij => qClockTerm_comm hpow factors hij)]
  simp only [qClockTerm_pow hpow, Finset.sum_smul]

end FiniteFourier
end LinearAlgebra
end OAI
