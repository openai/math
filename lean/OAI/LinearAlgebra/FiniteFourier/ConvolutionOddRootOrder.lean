import OAI.LinearAlgebra.FiniteFourier.ConvolutionSmoothPacking
import Mathlib.Algebra.GCDMonoid.Finset

/-! # The odd common root order for packing at characteristic two

For axes congruent to three modulo four, the half-predecessors are odd.
Their least common multiple and the largest admissible power of three give
an odd divisor of the smooth root order.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- The root order for the local packing at two. -/
def atTwoRootOrder (P : Finset ℕ) (B : ℕ) : ℕ :=
  Nat.lcm (P.lcm fun p ↦ (p - 1) / 2) (3 ^ Nat.log 3 (8 * B))

private lemma odd_nat_lcm {m n : ℕ} (hm : Odd m) (hn : Odd n) : Odd (Nat.lcm m n) :=
  (hm.mul hn).of_dvd_nat (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))

lemma atTwoRootOrder_odd {P : Finset ℕ} {B : ℕ} (hP : ∀ p ∈ P, p % 4 = 3) :
    Odd (atTwoRootOrder P B) := by
  apply odd_nat_lcm _ (show Odd (3 : ℕ) by decide).pow
  induction P using Finset.induction_on with
  | empty => simp
  | insert p P hp ih =>
    rw [Finset.lcm_insert]
    apply odd_nat_lcm
    · have := hP p (Finset.mem_insert_self p P)
      rw [Nat.odd_iff]
      omega
    · exact ih fun q hq ↦ hP q (Finset.mem_insert_of_mem hq)

lemma half_predecessor_dvd_atTwoRootOrder {P : Finset ℕ} {B p : ℕ} (hp : p ∈ P) :
    (p - 1) / 2 ∣ atTwoRootOrder P B :=
  (Finset.dvd_lcm (f := fun q ↦ (q - 1) / 2) hp).trans (Nat.dvd_lcm_left _ _)

lemma three_pow_dvd_atTwoRootOrder {P : Finset ℕ} {B k : ℕ} (hk : 3 ^ k ≤ 8 * B) :
    3 ^ k ∣ atTwoRootOrder P B :=
  (pow_dvd_pow 3 (Nat.le_log_of_pow_le (by decide) hk)).trans (Nat.dvd_lcm_right _ _)

lemma atTwoRootOrder_dvd_smoothRootOrder {P : Finset ℕ} {B : ℕ} {η : ℝ}
    (hP : ∀ p ∈ P, p ∈ smoothPredecessorPrimes (B : ℝ) η)
    (hcut : 3 ≤ (B : ℝ) ^ (1 - η)) :
    atTwoRootOrder P B ∣ smoothRootOrder B η := by
  apply Nat.lcm_dvd
  · apply Finset.lcm_dvd
    intro p hp
    have hmem := hP p hp
    obtain ⟨hprime, h3, _, _⟩ := (mem_smoothPredecessorPrimes (Nat.cast_nonneg B)).mp hmem
    have heven := (hprime.even_sub_one (by omega)).two_dvd
    exact (Nat.div_dvd_of_dvd heven).trans (predecessor_dvd_smoothRootOrder (Nat.cast_nonneg B) hmem)
  · have hthree : 3 ∈ Nat.primesLE ⌊(B : ℝ) ^ (1 - η)⌋₊ :=
      Nat.mem_primesLE.mpr ⟨Nat.le_floor (by simpa using hcut), Nat.prime_three⟩
    have hfloor : ⌊8 * (B : ℝ)⌋₊ = 8 * B := by
      rw [show (8 : ℝ) * B = ((8 * B : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast]
    simpa only [smoothRootOrder, hfloor] using
      (Finset.dvd_prod_of_mem (fun q : ℕ ↦ q ^ Nat.log q ⌊8 * (B : ℝ)⌋₊) hthree)

end FiniteFourier
end LinearAlgebra
end OAI
