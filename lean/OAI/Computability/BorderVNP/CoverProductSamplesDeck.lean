import OAI.Computability.BorderVNP.CoverProductSamples
import OAI.Computability.BorderVNP.CoverDeckTower

/-!
# Rational pack samples with uniform permutation and post-translation of deck labels

A pack chooses its speed permutation, one motion word per surface factor, and one deck
translation per factor. The pre-translation deck address can depend on the permutation and
on every word. Uniform post-translation still makes the resulting address uniform
conditionally on these choices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Hecke

open Finset Set MeasureTheory BorderVNP.Cover
open scoped Classical

variable {G I : Type*} [Group G] (Γ : Subgroup G) (z : G)
    [Fintype (Cosets (intersection Γ z))] [Fintype I]

/-- A finite sample for the whole pack, with the speed permutation and all deck translations. -/
abbrev PackSample (I : Type*) (d n : ℕ) := Equiv.Perm I × ProductSample Γ z I n × (I → Deck d)

/-- Exact weight of one pack sample. Deck labels are independent and uniform on the product. -/
noncomputable def packWeight {d n : ℕ} (s : PackSample Γ z I d n) : ℚ :=
  ((Fintype.card (Equiv.Perm I) : ℚ) * Fintype.card (I → Deck d))⁻¹ * productWeight Γ z n s.2.1

/-- Every sample has strictly positive rational weight. -/
theorem packWeight_pos {d n : ℕ} (s : PackSample Γ z I d n) : 0 < packWeight Γ z s := by
  unfold packWeight
  exact mul_pos (by positivity) (productWeight_pos Γ z n _)

/-- The pack probabilities, including the permutation and deck choices, sum to one in ℚ. -/
theorem sum_packWeight (d n : ℕ) : ∑ s : PackSample Γ z I d n, packWeight Γ z s = 1 := by
  have hd : (Fintype.card (I → Deck d) : ℚ) ≠ 0 := by positivity
  have hp : (Fintype.card (Equiv.Perm I) : ℚ) ≠ 0 := by positivity
  simp only [packWeight, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, ← Finset.mul_sum, sum_productWeight, mul_one]
  field_simp

/-- A left post-translation, coordinate by coordinate, of any pre-existing deck address. -/
def shiftedAddress {d : ℕ} (h a : I → Deck d) : I → Deck d := h * a

/-- Conditional on all frame motions, summing over deck labels erases dependence on the old
address. It is the finite right-multiplication permutation of the product deck group. -/
theorem sum_shiftedAddress {d : ℕ} {R : Type*} [AddCommMonoid R] (a : I → Deck d)
    (test : (I → Deck d) → R) : ∑ h, test (shiftedAddress h a) = ∑ h, test h :=
  Equiv.sum_comp (Equiv.mulRight a) test

variable [MeasurableSpace (Cosets Γ)]

/-- The exact event mean of the actual finite pack samples. The expected value is the uniform
average of the true frame event probabilities over permutations and destination addresses.
The address before translation may depend arbitrarily on the selected words. -/
theorem pack_event_mean {d n : ℕ} (x : Equiv.Perm I → I → G)
    (a : Equiv.Perm I → ProductSample Γ z I n → I → Deck d)
    (B : Equiv.Perm I → (I → Deck d) → Set (I → Cosets Γ)) (hB : ∀ π h, MeasurableSet (B π h)) :
    (∑ s : PackSample Γ z I d n, (packWeight Γ z s : ℝ) *
      (B s.1 (shiftedAddress s.2.2 (a s.1 s.2.1))).indicator 1 (productPoint Γ z n (x s.1) s.2.1)) =
    ((Fintype.card (Equiv.Perm I) : ℝ) * Fintype.card (I → Deck d))⁻¹ *
      ∑ π, ∑ h, (productLaw Γ z n (x π)).toMeasure.real (B π h) := by
  simp only [packWeight, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Fintype.sum_prod_type,
    mul_assoc, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  have hr (w : ProductSample Γ z I n) :
      (∑ h, (B π (shiftedAddress h (a π w))).indicator (1 : (I → Cosets Γ) → ℝ)
        (productPoint Γ z n (x π) w)) =
      ∑ h, (B π h).indicator 1 (productPoint Γ z n (x π) w) :=
    sum_shiftedAddress (a π w) (fun h => (B π h).indicator 1 (productPoint Γ z n (x π) w))
  simp_rw [hr]
  simp_rw [productLaw_real Γ z n (x π) _ (hB π _)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- For an individual destination address the expected indicator count is the corresponding
frame bin probability, averaged over permutations and divided by the number of product tiles. -/
theorem pack_single_address_mean {d n : ℕ} (x : Equiv.Perm I → I → G)
    (a : Equiv.Perm I → ProductSample Γ z I n → I → Deck d) (h₀ : I → Deck d)
    (B : Equiv.Perm I → Set (I → Cosets Γ)) (hB : ∀ π, MeasurableSet (B π)) :
    (∑ s : PackSample Γ z I d n, (packWeight Γ z s : ℝ) *
      (if shiftedAddress s.2.2 (a s.1 s.2.1) = h₀ then
        (B s.1).indicator 1 (productPoint Γ z n (x s.1) s.2.1) else 0)) =
    ((Fintype.card (Equiv.Perm I) : ℝ) * Fintype.card (I → Deck d))⁻¹ *
      ∑ π, (productLaw Γ z n (x π)).toMeasure.real (B π) := by
  let E (π : Equiv.Perm I) (h : I → Deck d) := if h = h₀ then B π else ∅
  have he π h : MeasurableSet (E π h) := by by_cases hh : h = h₀ <;> simp [E,hh,hB]
  have hb π h y : (E π h).indicator (1 : (I → Cosets Γ) → ℝ) y =
      if h = h₀ then (B π).indicator 1 y else 0 := by by_cases hh : h = h₀ <;> simp [E,hh]
  have hsum π : (∑ h, (productLaw Γ z n (x π)).toMeasure.real (E π h)) =
      (productLaw Γ z n (x π)).toMeasure.real (B π) := by
    rw [Finset.sum_eq_single h₀]
    · simp [E]
    · intro h _ hn; simp [E,hn]
    · simp
  simpa only [hb, hsum] using pack_event_mean Γ z x a E he

end Hecke

end BorderVNP
end Computability
end OAI
