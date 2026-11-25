import OAI.LinearAlgebra.FiniteFourier.ConvolutionPrimeColoring
import OAI.LinearAlgebra.FiniteFourier.ConvolutionSmoothPacking
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.GCD.Prime

/-! # Root orders for the two lists of prime axes

The order for each list combines its predecessor lengths with the largest power
of two allowed by the transform width. Every odd prime dividing this order or
an axis length occurs in the support of a member of the list.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset

/-- The transform order for a list of axes and maximum dyadic width `K`. -/
def axisRootOrder (axes : Finset ℕ) (K : ℕ) : ℕ :=
  Nat.lcm (2 ^ Nat.log 2 K) (axes.lcm (· - 1))

theorem axisRootOrder_pos {axes : Finset ℕ} (K : ℕ) (haxes : ∀ p ∈ axes, 2 ≤ p) :
    0 < axisRootOrder axes K := by
  apply Nat.lcm_pos (by positivity)
  apply Nat.pos_of_ne_zero
  exact lcm_ne_zero_iff.mpr fun p hp => by have := haxes p hp; omega

theorem predecessor_dvd_axisRootOrder {axes : Finset ℕ} (K : ℕ) {p : ℕ} (hp : p ∈ axes) :
    p - 1 ∣ axisRootOrder axes K :=
  (dvd_lcm (f := (· - 1)) hp).trans (Nat.dvd_lcm_right _ _)

theorem two_pow_dvd_axisRootOrder (axes : Finset ℕ) {k K : ℕ} (hk : 2^k ≤ K) :
    2^k ∣ axisRootOrder axes K :=
  (pow_dvd_pow 2 (Nat.le_log_of_pow_le Nat.one_lt_two hk)).trans (Nat.dvd_lcm_left _ _)

/-- Odd primes occurring in the list's order or volume divide the product of
a single axis length and its predecessor. -/
theorem exists_axis_of_odd_prime_dvd_rootOrder_mul_prod {axes : Finset ℕ} {K l : ℕ}
    (hl : l.Prime) (hodd : l ≠ 2) (hd : l ∣ axisRootOrder axes K * ∏ p ∈ axes, p) :
    ∃ p ∈ axes, l ∣ p * (p - 1) := by
  rcases hl.dvd_mul.mp hd with h | h
  · rcases hl.dvd_or_dvd_of_dvd_lcm h with htwo | hpred
    · exact (hodd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp
        (hl.dvd_of_dvd_pow htwo))).elim
    · obtain ⟨p, hp, hd⟩ := (hl.prime.dvd_finsetProd_iff (fun a : ℕ => a - 1)).mp
        (hpred.trans (lcm_dvd_prod axes _))
      exact ⟨p, hp, dvd_mul_of_dvd_right hd _⟩
  · obtain ⟨p, hp, hd⟩ := (hl.prime.dvd_finsetProd_iff id).mp h
    exact ⟨p, hp, dvd_mul_of_dvd_left hd _⟩

/-- Disjoint odd supports give disjoint odd prime divisors of the two
order-times-volume products. -/
theorem odd_prime_not_dvd_both_axisRootOrders {R S : Finset ℕ} (K : ℕ)
    (hd : ∀ p ∈ R, ∀ q ∈ S, ∀ l : ℕ, l.Prime → l ≠ 2 →
      l ∣ p * (p - 1) → ¬ l ∣ q * (q - 1))
    {l : ℕ} (hl : l.Prime) (ho : l ≠ 2) :
    l ∣ axisRootOrder R K * ∏ p ∈ R, p → ¬ l ∣ axisRootOrder S K * ∏ q ∈ S, q := by
  intro hr hs
  obtain ⟨p, hp, hpr⟩ := exists_axis_of_odd_prime_dvd_rootOrder_mul_prod hl ho hr
  obtain ⟨q, hq, hqs⟩ := exists_axis_of_odd_prime_dvd_rootOrder_mul_prod hl ho hs
  exact hd p hp q hq l hl ho hpr hqs

/-- Packing may select subsets of the two lists after fixing their root
orders. The two resulting order-times-volume products still have disjoint
odd prime divisors. -/
theorem odd_prime_not_dvd_both_packedOrders {R S R' S' : Finset ℕ} (K : ℕ)
    (hR : R' ⊆ R) (hS : S' ⊆ S)
    (hd : ∀ p ∈ R, ∀ q ∈ S, ∀ l : ℕ, l.Prime → l ≠ 2 →
      l ∣ p * (p - 1) → ¬ l ∣ q * (q - 1))
    {l : ℕ} (hl : l.Prime) (ho : l ≠ 2) :
    l ∣ axisRootOrder R K * ∏ p ∈ R', p → ¬ l ∣ axisRootOrder S K * ∏ q ∈ S', q := by
  intro hr hs
  apply odd_prime_not_dvd_both_axisRootOrders K hd hl ho
  · exact hr.trans (mul_dvd_mul_left _ (prod_dvd_prod_of_subset _ _ id hR))
  · exact hs.trans (mul_dvd_mul_left _ (prod_dvd_prod_of_subset _ _ id hS))

/-- In a dyadic interval above two, every eligible axis belongs to the
full list of primes with smooth predecessor. -/
theorem dyadicEligibleAxes_subset_smoothPredecessorPrimes {B : ℕ} {η : ℝ} (hB : 4 ≤ B) :
    dyadicEligibleAxes B η ⊆ smoothPredecessorPrimes B η := by
  intro p hp
  obtain ⟨⟨hl, hu⟩, hpr, hs⟩ := mem_dyadicEligibleAxes.mp hp
  exact (mem_smoothPredecessorPrimes (Nat.cast_nonneg B)).mpr
    ⟨hpr, by omega, Nat.cast_le.mpr hu, hs⟩

/-- A list supported on smooth predecessors has order dividing the common
smooth order, so the common logarithmic cost bound applies to either list. -/
theorem axisRootOrder_dvd_smoothRootOrder {axes : Finset ℕ} {B η : ℝ}
    (hB : 1 ≤ B) (hcut : 2 ≤ B ^ (1-η))
    (haxes : axes ⊆ smoothPredecessorPrimes B η) :
    axisRootOrder axes ⌊8*B⌋₊ ∣ smoothRootOrder B η := by
  apply Nat.lcm_dvd
  · apply two_pow_dvd_smoothRootOrder hcut
    have hfloor : 1 ≤ ⌊8*B⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact (Nat.cast_le.mpr (Nat.pow_log_le_self 2 (by omega : ⌊8*B⌋₊ ≠ 0))).trans
      (Nat.floor_le (by linarith))
  · exact lcm_dvd fun p hp => predecessor_dvd_smoothRootOrder (by linarith) (haxes hp)

end FiniteFourier
end LinearAlgebra
end OAI
