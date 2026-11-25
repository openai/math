import OAI.Computability.BorderVNP.CoverProductSamplesDeck
import OAI.Computability.BorderVNP.ShortenEpochConcentration

/-!
# Counts of the actual wires in one moved pack

All wires in a given pack use one common permutation, one tuple of motion words and one
tuple of deck post-translations. Linearity of expectation identifies the exact rational
mean of these integer counts with a sum of frame bin probabilities, without requiring
independence between wires of the pack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Hecke

open MeasureTheory Set Finset BorderVNP.Cover
open scoped Classical

variable {G I W : Type*} [Group G] (Γ : Subgroup G) (z : G) [Fintype (Cosets (intersection Γ z))]
    [Fintype I] [MeasurableSpace (Cosets Γ)] {d n : ℕ}

/-- Count wires of a pack arriving in the given tile and the indicated frame event. -/
noncomputable def packBinCount (wire : Finset W) (x : W → Equiv.Perm I → I → G)
    (a : W → Equiv.Perm I → ProductSample Γ z I n → I → Deck d) (tile : I → Deck d)
    (B : W → Equiv.Perm I → Set (I → Cosets Γ)) (s : PackSample Γ z I d n) : ℕ :=
  (wire.filter fun e => shiftedAddress s.2.2 (a e s.1 s.2.1) = tile ∧
    productPoint Γ z n (x e s.1) s.2.1 ∈ B e s.1).card

omit [Fintype (Cosets (intersection Γ z))] [MeasurableSpace (Cosets Γ)] in
/-- The actual count of distinct wire records (also when their positions coincide) is
bounded by the total number of wire records in the pack. -/
theorem packBinCount_le (wire : Finset W) (x : W → Equiv.Perm I → I → G)
    (a : W → Equiv.Perm I → ProductSample Γ z I n → I → Deck d) (tile : I → Deck d)
    (B : W → Equiv.Perm I → Set (I → Cosets Γ)) (s : PackSample Γ z I d n) :
    packBinCount Γ z wire x a tile B s ≤ wire.card := Finset.card_filter_le ..

/-- Exact expectation of an integer count in a shared pack motion, expressed as the
permutation-averaged sum of individual frame event probabilities divided by the tile count. -/
theorem packBinCount_mean (wire : Finset W) (x : W → Equiv.Perm I → I → G)
    (a : W → Equiv.Perm I → ProductSample Γ z I n → I → Deck d) (tile : I → Deck d)
    (B : W → Equiv.Perm I → Set (I → Cosets Γ)) (hB : ∀ e π, MeasurableSet (B e π)) :
    (↑(∑ s : PackSample Γ z I d n, packWeight Γ z s * (packBinCount Γ z wire x a tile B s : ℚ)) : ℝ) =
      ((Fintype.card (Equiv.Perm I) : ℝ) * Fintype.card (I → Deck d))⁻¹ *
        ∑ e ∈ wire, ∑ π, (productLaw Γ z n (x e π)).toMeasure.real (B e π) := by
  push_cast
  simp only [packBinCount, Finset.natCast_card_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have h := pack_single_address_mean Γ z (x e) (a e) tile (B e) (hB e)
  convert h using 1
  · apply Finset.sum_congr rfl
    intro s _
    by_cases ha : shiftedAddress s.2.2 (a e s.1 s.2.1) = tile <;>
      by_cases he : productPoint Γ z n (x e s.1) s.2.1 ∈ B e s.1 <;> simp [ha,he]
  · simp only [Finset.mul_sum]

omit [MeasurableSpace (Cosets Γ)] in
/-- Sampling independently across packs with these rational weights instantiates the
variance bound on the actual natural-valued bin tables. Within each pack one sample is
used for every wire. -/
theorem exists_concentrated_packSamples {P J : Type*} [Fintype P] [Nonempty P] [Fintype J]
    (counts : P → PackSample Γ z I d n → J → ℕ) {tiles radius : ℝ}
    (ht : 0 ≤ tiles) (hr : 0 ≤ radius)
    (hbound : ∀ i s, tiles * Epoch.binEnergy (fun b => (counts i s b : ℝ)) ≤ radius^2) :
    ∃ ω : P → PackSample Γ z I d n, Real.sqrt tiles *
      Real.sqrt (Epoch.binEnergy (fun b => (∑ i, (counts i (ω i) b : ℝ)) / Fintype.card P -
        (∑ i, ∑ s, (packWeight Γ z s : ℝ) * counts i s b) / Fintype.card P)) ≤
      radius / Real.sqrt (Fintype.card P) := by
  apply Epoch.exists_concentrated_motions (fun _ s => (packWeight Γ z s : ℝ))
    (fun _ s => Rat.cast_nonneg.mpr (packWeight_pos Γ z s).le) _
    (fun i s b => (counts i s b : ℝ)) ht hr hbound
  intro _
  exact_mod_cast sum_packWeight (I := I) Γ z d n

end Hecke

end BorderVNP
end Computability
end OAI
