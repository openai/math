import OAI.LinearAlgebra.FiniteFourier.PrimeBitLetter
import OAI.LinearAlgebra.FiniteFourier.PrimeRoutingGram

/-! # The bit rectangles for the Hamming-distance correction

A cut at one position records either an entire common letter or the two
letters' common prefix and the source bit at their first disagreement.
The records at different positions are chosen independently.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Classical

abbrev BitLabel (L b : ℕ) := Fin L → BitLetter b
abbrev BitCuts (L b : ℕ) := Fin L → Option (Fin b)

/-- Each pattern specifies which letter data to retain at each position. -/
abbrev BitRectangle (L b : ℕ) := (c : BitCuts L b) × (∀ i, BitRecord b (c i))

variable {L b : ℕ}

private def bitEndpoint (record : ∀ c : Option (Fin b), BitLetter b → BitRecord b c)
    (R : BitRectangle L b) : Set (BitLabel L b) :=
  {v | ∀ i, R.2 i = record (R.1 i) (v i)}

/-- The source side of the rectangle. -/
def bitSources (R : BitRectangle L b) : Set (BitLabel L b) := bitEndpoint leftBitRecord R

/-- The target side of the rectangle. At a cut the target bit is opposite to the stored bit. -/
def bitTargets (R : BitRectangle L b) : Set (BitLabel L b) := bitEndpoint rightBitRecord R

private def bitEndpointEquiv (record : ∀ c : Option (Fin b), BitLetter b → BitRecord b c)
    (v : BitLabel L b) : BitCuts L b ≃ {R : BitRectangle L b // v ∈ bitEndpoint record R} where
  toFun c := ⟨⟨c, fun i => record (c i) (v i)⟩, fun _ => rfl⟩
  invFun R := R.1.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨c, data⟩, hd⟩
    apply Subtype.ext
    exact congrArg (Sigma.mk c) (funext fun i => (hd i).symm)

/-- Every source label occurs in exactly one rectangle per cut pattern. -/
theorem card_bitSource_incidence (v : BitLabel L b) :
    Fintype.card {R : BitRectangle L b // v ∈ bitSources R} = (1 + b) ^ L := by
  calc
    _ = Fintype.card (BitCuts L b) := Fintype.card_congr (bitEndpointEquiv leftBitRecord v).symm
    _ = _ := by simp [BitCuts, Nat.add_comm]

/-- The same incidence count holds on the target side. -/
theorem card_bitTarget_incidence (w : BitLabel L b) :
    Fintype.card {R : BitRectangle L b // w ∈ bitTargets R} = (1 + b) ^ L := by
  calc
    _ = Fintype.card (BitCuts L b) := Fintype.card_congr (bitEndpointEquiv rightBitRecord w).symm
    _ = _ := by simp [BitCuts, Nat.add_comm]

/-- The products of the one-letter rectangles partition all ordered pairs of labels. -/
theorem existsUnique_bitRectangle (v w : BitLabel L b) :
    ∃! R : BitRectangle L b, v ∈ bitSources R ∧ w ∈ bitTargets R := by
  classical
  choose c hc using fun i => (existsUnique_bitCut (v i) (w i)).exists
  refine ⟨⟨c, fun i => leftBitRecord (c i) (v i)⟩, ⟨fun _ => rfl, hc⟩, ?_⟩
  rintro ⟨c', data⟩ ⟨hs, ht⟩
  have hcut : c' = c := funext fun i =>
    (existsUnique_bitCut (v i) (w i)).unique ((hs i).symm.trans (ht i)) (hc i)
  subst c'
  exact congrArg (Sigma.mk c) (funext hs)

/-- Index a bit letter by the corresponding alphabet of size `2 ^ b`. -/
def bitLetterIndex (b : ℕ) : BitLetter b ≃ Fin (2 ^ b) :=
  Fintype.equivFinOfCardEq (by simp [BitLetter])

/-- Convert each letter into an index of the Hamming Gram matrix. -/
def bitLabelIndex (L b : ℕ) : BitLabel L b ≃ RoutingLabel L (2 ^ b) :=
  Equiv.piCongrRight fun _ => bitLetterIndex b

/-- The number of positions cutting at a first differing bit. -/
def bitCutDistance (c : BitCuts L b) : ℕ := ∑ i, if c i = none then 0 else 1

/-- Every pair on a rectangle has the same exact Hamming distance. -/
theorem routingDistance_bitRectangle (R : BitRectangle L b) {v w : BitLabel L b}
    (hs : v ∈ bitSources R) (ht : w ∈ bitTargets R) :
    routingDistance (bitLabelIndex L b v) (bitLabelIndex L b w) = bitCutDistance R.1 := by
  apply Finset.sum_congr rfl
  intro i _
  have he := eq_iff_cut_none ((hs i).symm.trans (ht i))
  change (if bitLetterIndex b (v i) = bitLetterIndex b (w i) then 0 else 1) = _
  simp only [Equiv.apply_eq_iff_eq, he]

/-- Every nondivisible cut pattern is a rectangle of mutually orthogonal source/target pairs. -/
theorem routingGram_bitRectangle_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] (R : BitRectangle L b)
    (hd : ¬ ℓ ∣ bitCutDistance R.1) {v w : BitLabel L b}
    (hs : v ∈ bitSources R) (ht : w ∈ bitTargets R) :
    routingGram ℓ L (2 ^ b) (bitLabelIndex L b v) (bitLabelIndex L b w) = 0 := by
  simp only [routingGram_apply, routingDistance_bitRectangle R hs ht, ite_eq_right hd]

/-- Rectangles at distances nonzero modulo `ℓ`, with any coefficient depending
only on distance, sum to the indicated correction matrix entry. -/
theorem sum_freeBitRectangle_weights {A : Type*} [AddCommMonoid A] (weight : ℕ → A)
    (ℓ : ℕ) (v w : BitLabel L b) :
    (∑ R : BitRectangle L b,
      if v ∈ bitSources R ∧ w ∈ bitTargets R ∧ ¬ℓ ∣ bitCutDistance R.1
      then weight (bitCutDistance R.1) else 0) =
    let d := routingDistance (bitLabelIndex L b v) (bitLabelIndex L b w)
    if ℓ ∣ d then 0 else weight d := by
  obtain ⟨R, hR, huniq⟩ := existsUnique_bitRectangle v w
  rw [Finset.sum_eq_single R, routingDistance_bitRectangle R hR.1 hR.2]
  · by_cases hd : ℓ ∣ bitCutDistance R.1 <;> simp [hR.1, hR.2, hd]
  · intro R' _ hne
    apply ite_eq_right
    exact fun h => hne (huniq R' ⟨h.1, h.2.1⟩)
  · simp

end

end

end FiniteFourier
end LinearAlgebra
end OAI
