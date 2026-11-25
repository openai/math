import OAI.LinearAlgebra.FiniteFourier.FractionFreeWires
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.PrimeFin

/-! # Prime support of cleared denominators

The first dyadic list has finitely many odd denominator primes. A second list
that avoids all of them has only a power of two in common with the first scale.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- Denominators coprime to each member of a prescribed finite list. -/
def denominatorsAvoiding (L : Finset ℕ) : Submonoid ℕ where
  carrier := {d | ∀ p ∈ L, Nat.Coprime p d}
  one_mem' := by simp
  mul_mem' ha hb p hp := (ha p hp).mul_right (hb p hp)

@[simp] theorem mem_denominatorsAvoiding {L : Finset ℕ} {d : ℕ} :
    d ∈ denominatorsAvoiding L ↔ ∀ p ∈ L, Nat.Coprime p d := Iff.rfl

/-- The original LCM alignment is valid for every finite set of forbidden primes. -/
def WireAlignment.avoiding (L : Finset ℕ) : WireAlignment (denominatorsAvoiding L) :=
  .lcm _ fun {a b} ha hb p hp =>
    Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul a b) ((ha p hp).mul_right (hb p hp))

/-- Avoiding the prime two gives an odd integer scale for the positive list. -/
theorem odd_of_mem_denominatorsAvoiding_two {d : ℕ} (hd : d ∈ denominatorsAvoiding {2}) :
    Odd d := Nat.coprime_two_left.mp (hd 2 (Finset.mem_singleton_self 2))

/-- The observed odd denominator primes of the first dyadic scale are
disjoint from every prime that was protected in its construction. -/
theorem disjoint_oddFactors_of_mem_denominatorsAvoiding {L : Finset ℕ} {D : ℕ}
    (hD : D ∈ denominatorsAvoiding L) : Disjoint (D.primeFactors.erase 2) L := by
  apply Finset.disjoint_left.mpr
  intro p hp hL
  obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp (Finset.mem_of_mem_erase hp)
  exact hprime.coprime_iff_not_dvd.mp (hD p hL) hdvd

/-- An odd-prime-free gcd is a power of two, including the value one. -/
theorem gcd_eq_pow_two_of_common_prime {D₁ D₂ : ℕ} (hD₁ : 0 < D₁)
    (h : ∀ p, Nat.Prime p → p ∣ D₁ → p ∣ D₂ → p = 2) :
    ∃ k, Nat.gcd D₁ D₂ = 2 ^ k := by
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.gcd_pos_of_pos_left _ hD₁).ne' ?_⟩
  exact fun hp hpd => h _ hp (hpd.trans (Nat.gcd_dvd_left ..)) (hpd.trans (Nat.gcd_dvd_right ..))

theorem gcd_eq_pow_two_of_avoids_oddFactors {D₁ D₂ : ℕ} (hD₁ : 0 < D₁)
    (hD₂ : D₂ ∈ denominatorsAvoiding (D₁.primeFactors.erase 2)) :
    ∃ k, Nat.gcd D₁ D₂ = 2 ^ k := by
  apply gcd_eq_pow_two_of_common_prime hD₁
  intro p hp hd₁ hd₂
  by_contra hn
  exact hp.coprime_iff_not_dvd.mp (hD₂ p (Finset.mem_erase.mpr
    ⟨hn, hp.mem_primeFactors hd₁ hD₁.ne'⟩)) hd₂

end FiniteFourier
end LinearAlgebra
end OAI
