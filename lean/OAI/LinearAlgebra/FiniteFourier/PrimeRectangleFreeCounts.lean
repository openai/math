import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleWeights

/-! # Incidence costs of free rectangles

Deleting the rectangles at distances divisible by the prime leaves at most
one incident rectangle per cut pattern at a fixed endpoint. Summing this
per-label bound controls the combined work at all free endpoints.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped Classical

variable {L b : ℕ}

private theorem card_freeBit_incidence_le (ℓ : ℕ) (P : BitRectangle L b → Prop) :
    Fintype.card {R : FreeBitRectangle ℓ L b // P R.val} ≤
      Fintype.card {R : BitRectangle L b // P R} :=
  Fintype.card_le_of_injective (fun R => (⟨R.val.val, R.property⟩ : {R // P R}))
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun R : {R // P R} => R.val) h))

/-- A fixed source can use at most one free rectangle per cut pattern. -/
theorem card_freeBitSource_incidence_le (ℓ : ℕ) (v : BitLabel L b) :
    Fintype.card {R : FreeBitRectangle ℓ L b // v ∈ bitSources R.val} ≤ (1+b)^L := by
  exact (card_freeBit_incidence_le ℓ (fun R => v ∈ bitSources R)).trans_eq
    (card_bitSource_incidence v)

/-- A fixed target can use at most one free rectangle per cut pattern. -/
theorem card_freeBitTarget_incidence_le (ℓ : ℕ) (v : BitLabel L b) :
    Fintype.card {R : FreeBitRectangle ℓ L b // v ∈ bitTargets R.val} ≤ (1+b)^L := by
  exact (card_freeBit_incidence_le ℓ (fun R => v ∈ bitTargets R)).trans_eq
    (card_bitTarget_incidence v)

private theorem sum_card_bitEndpoints_le {T : Type*} [Fintype T]
    (E : T → Set (BitLabel L b))
    (h : ∀ v, Fintype.card {R // v ∈ E R} ≤ (1+b)^L) :
    (∑ R, Fintype.card {v // v ∈ E R}) ≤ (2^b)^L * (1+b)^L := by
  classical
  calc
    _ = ∑ v : BitLabel L b, Fintype.card {R // v ∈ E R} := by
      simp_rw [Fintype.card_subtype, Finset.card_filter]
      exact Finset.sum_comm
    _ ≤ ∑ _v : BitLabel L b, (1+b)^L := Finset.sum_le_sum fun v _ => h v
    _ = _ := by simp [BitLabel, BitLetter]

/-- Total source incidences over all free rectangles. -/
theorem sum_card_freeBitSources_le (ℓ L b : ℕ) :
    (∑ R : FreeBitRectangle ℓ L b, Fintype.card {v // v ∈ bitSources R.val}) ≤
      (2^b)^L * (1+b)^L :=
  sum_card_bitEndpoints_le (fun R : FreeBitRectangle ℓ L b => bitSources R.val)
    (card_freeBitSource_incidence_le ℓ)

/-- Total target incidences over all free rectangles. -/
theorem sum_card_freeBitTargets_le (ℓ L b : ℕ) :
    (∑ R : FreeBitRectangle ℓ L b, Fintype.card {v // v ∈ bitTargets R.val}) ≤
      (2^b)^L * (1+b)^L :=
  sum_card_bitEndpoints_le (fun R : FreeBitRectangle ℓ L b => bitTargets R.val)
    (card_freeBitTarget_incidence_le ℓ)

private theorem leftBitRecord_surjective (c : Option (Fin b)) :
    Function.Surjective (leftBitRecord c) := by
  cases c with
  | none => exact fun v => ⟨v, rfl⟩
  | some i =>
    rintro ⟨prefixBits, bit⟩
    let v : BitLetter b := fun j => if h : j.val < i.val then prefixBits ⟨j.val, h⟩ else bit
    refine ⟨v, Prod.ext (funext fun j => ?_) ?_⟩
    · change (if h : j.val < i.val then prefixBits ⟨j.val, h⟩ else bit) = prefixBits j
      rw [dite_eq_left j.isLt]
    · simp [leftBitRecord, v]

/-- Every source record can be completed to a full label. -/
theorem bitSources_nonempty (R : BitRectangle L b) : (bitSources R).Nonempty := by
  choose v hv using fun i => leftBitRecord_surjective (R.1 i) (R.2 i)
  exact ⟨v, fun i => (hv i).symm⟩

/-- Every free rectangle contributes at least one source incidence. -/
theorem card_freeBitRectangle_le (ℓ L b : ℕ) :
    Fintype.card (FreeBitRectangle ℓ L b) ≤ (2^b)^L * (1+b)^L := by
  apply le_trans _ (sum_card_freeBitSources_le ℓ L b)
  calc
    _ = ∑ _ : FreeBitRectangle ℓ L b, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun R _ => Fintype.card_pos_iff.mpr
      (bitSources_nonempty R.val).to_subtype

end FiniteFourier
end LinearAlgebra
end OAI
