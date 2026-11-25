import OAI.LinearAlgebra.FiniteFourier.PrimeBitRectangles
import OAI.LinearAlgebra.FiniteFourier.PrimeRoutingPolynomial

/-! # Distance weights of the prime Fourier rectangles

On the multiples of the prime step, binomial interpolation on the number of
matching letters gives the diagonal indicator. On every other distance the
unique free rectangle supplies the negative of this weight.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Classical

variable {L b q : ℕ}

theorem routingDistance_le (v w : RoutingLabel L q) : routingDistance v w ≤ L := by
  calc
    _ ≤ ∑ _ : Fin L, 1 := Finset.sum_le_sum fun i _ => by
      split <;> decide
    _ = _ := by simp

@[simp] theorem routingDistance_eq_zero_iff (v w : RoutingLabel L q) :
    routingDistance v w = 0 ↔ v = w := by
  constructor
  · intro h
    funext i
    have hi := (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)
    by_contra hne
    simp [hne] at hi
  · rintro rfl
    simp [routingDistance]

/-- The total contribution from weighted common restrictions at Hamming distance `k`. -/
def chargedDistanceWeight {K : Type*} [Semiring K] {t : ℕ}
    (u : Fin (t+1) → K) (L k : ℕ) : K :=
  ∑ j, (((L - k).choose j.val : ℕ) : K) * u j

/-- The binomial weights pick out the diagonal among all distances divisible by `ℓ`. -/
theorem exists_chargedDistanceWeight (K : Type*) [CommRing K] (ℓ L : ℕ)
    (hℓ : 0 < ℓ) (hu : IsUnit (ℓ : K)) :
    ∃ u : Fin (L / ℓ + 1) → K, ∀ k ≤ L, ℓ ∣ k →
      chargedDistanceWeight u L k = if k = 0 then 1 else 0 := by
  obtain ⟨u, hu'⟩ := exists_charged_coefficients K (L % ℓ) ℓ (L / ℓ) hu
  refine ⟨u, fun k hk hd => ?_⟩
  obtain ⟨c, rfl⟩ := hd
  have hc : c ≤ L / ℓ := (Nat.le_div_iff_mul_le hℓ).mpr (by rwa [Nat.mul_comm])
  have hcut : L - ℓ * c = L % ℓ + ℓ * (L / ℓ - c) := by
    rw [Nat.mul_sub]
    have h := Nat.mod_add_div L ℓ
    have hmul := Nat.mul_le_mul_left ℓ hc
    omega
  have heq : L / ℓ - c = L / ℓ ↔ ℓ * c = 0 := by
    rw [Nat.mul_eq_zero]
    omega
  simpa only [chargedDistanceWeight, hcut, heq] using hu' (L / ℓ - c) (Nat.sub_le ..)

/-- A free bit rectangle has a single exact Hamming distance, nonzero modulo `ℓ`. -/
abbrev FreeBitRectangle (ℓ L b : ℕ) := {R : BitRectangle L b // ¬ℓ ∣ bitCutDistance R.1}

/-- Removing rectangles of divisible distance leaves the weighted correction. -/
theorem sum_freeRectangle_weights {K : Type*} [AddCommMonoid K] (weight : ℕ → K)
    (ℓ : ℕ) (v w : BitLabel L b) :
    (∑ R : FreeBitRectangle ℓ L b,
      if v ∈ bitSources R.val ∧ w ∈ bitTargets R.val then weight (bitCutDistance R.val.1) else 0) =
    let d := routingDistance (bitLabelIndex L b v) (bitLabelIndex L b w)
    if ℓ ∣ d then 0 else weight d := by
  rw [← sum_freeBitRectangle_weights weight ℓ v w]
  trans ∑ R ∈ Finset.univ.filter (fun R : BitRectangle L b => ¬ℓ ∣ bitCutDistance R.1),
      if v ∈ bitSources R ∧ w ∈ bitTargets R then weight (bitCutDistance R.1) else 0
  · simpa only [Finset.subtype_univ] using Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
      (fun R : BitRectangle L b => if v ∈ bitSources R ∧ w ∈ bitTargets R
        then weight (bitCutDistance R.1) else 0) (p := fun R => ¬ℓ ∣ bitCutDistance R.1)
  · simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro R _
    split_ifs <;> simp_all

end

end

end FiniteFourier
end LinearAlgebra
end OAI
