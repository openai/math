import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleWeights
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleCounts

/-! # Weighted rectangles realizing identity routing in the prime Fourier kernel

Each charged rectangle uses one common restriction on both endpoints. Each free
rectangle uses the first-disagreement partition. Its sources and targets have
zero pairing, so their endpoint Fourier transforms can be shared across queries.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Classical

/-- Weighted identity routing together with the diagonal form on common coordinates. -/
structure PrimeRectangleSystem (K : Type*) [CommRing K] (ℓ L b : ℕ) where
  D : ℕ
  dimension_le : D ≤ 1 + (1 + L * 2^b)^(ℓ-1)
  a : Fin D → ZMod ℓ
  d : BitLabel L b → Fin D → ZMod ℓ
  diagonal_ne_zero : ∀ i, a i ≠ 0
  gram : ∀ v w, ∑ i, a i * d v i * d w i =
    routingGram ℓ L (2^b) (bitLabelIndex L b v) (bitLabelIndex L b w)
  chargedWeight : ChargedRectangle L b (L / ℓ) → K
  freeWeight : FreeBitRectangle ℓ L b → K
  identity : ∀ v w : BitLabel L b,
    (∑ R, if v ∈ chargedEndpoint R ∧ w ∈ chargedEndpoint R then chargedWeight R else 0) +
    (∑ R : FreeBitRectangle ℓ L b, if v ∈ bitSources R.val ∧ w ∈ bitTargets R.val
      then freeWeight R else 0) = if v = w then 1 else 0

namespace PrimeRectangleSystem

variable {K : Type*} [CommRing K] {ℓ L b : ℕ} [Fact ℓ.Prime] (S : PrimeRectangleSystem K ℓ L b)

/-- The distinguished direction at each label has unit norm. -/
theorem norm_one (v : BitLabel L b) : ∑ i, S.a i * S.d v i * S.d v i = 1 := by
  rw [S.gram, routingGram_self]

/-- There is at least one common coordinate. -/
theorem dimension_pos : 0 < S.D := by
  by_contra! h
  have hn := S.norm_one (fun _ _ => false)
  have : IsEmpty (Fin S.D) := Fin.isEmpty_iff.mpr (Nat.eq_zero_of_le_zero h)
  simp at hn

/-- Opposite endpoints of a free rectangle are perpendicular in the common form. -/
theorem free_orthogonal (R : FreeBitRectangle ℓ L b) {v w : BitLabel L b}
    (hv : v ∈ bitSources R.val) (hw : w ∈ bitTargets R.val) :
    ∑ i, S.a i * S.d v i * S.d w i = 0 := by
  rw [S.gram]
  exact routingGram_bitRectangle_eq_zero R.val R.property hv hw

end PrimeRectangleSystem

/-- Identity routing over any coefficient ring in which the prime step is a unit. -/
theorem exists_primeRectangleSystem (K : Type*) [CommRing K] (ℓ L b : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : K)) : Nonempty (PrimeRectangleSystem K ℓ L b) := by
  obtain ⟨u, hu⟩ := exists_chargedDistanceWeight K ℓ L (Fact.out : ℓ.Prime).pos hℓ
  obtain ⟨D, hD, a, d, ha, hd, _⟩ := exists_routing_gram_vectors ℓ L (2^b)
  refine ⟨{ D := D, dimension_le := hD, a := a, d := fun v => d (bitLabelIndex L b v),
            diagonal_ne_zero := ha, gram := fun v w => hd _ _,
            chargedWeight := fun R => u R.1,
            freeWeight := fun R => -chargedDistanceWeight u L (bitCutDistance R.val.1),
            identity := ?_ }⟩
  intro v w
  rw [sum_chargedRectangle_weights, sum_freeRectangle_weights (fun k => -chargedDistanceWeight u L k)]
  let k := routingDistance (bitLabelIndex L b v) (bitLabelIndex L b w)
  change chargedDistanceWeight u L k + (if ℓ ∣ k then 0 else -chargedDistanceWeight u L k) = _
  have hk : k = 0 ↔ v = w := by simp [k]
  by_cases h : ℓ ∣ k
  · simp only [h, ite_true, add_zero, hu k (routingDistance_le ..) h, hk]
  · have hne : v ≠ w := fun h' => h ((hk.mpr h').symm ▸ dvd_zero ℓ)
    simp [h, hne]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
