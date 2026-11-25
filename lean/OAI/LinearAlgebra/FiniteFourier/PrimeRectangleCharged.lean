import OAI.LinearAlgebra.FiniteFourier.PrimeBitRectangles
import Mathlib.Data.Finset.Powerset

/-! # Charged rectangles on bit labels

A charged rectangle records a common restriction of the source and target labels
on a set of at most `t` positions. At degree `j` the rectangles containing a
pair of labels are indexed by the `j`-subsets of its agreement positions.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Classical

/-- Supports of charged rectangles of exactly degree `j`. -/
abbrev ChargedSupport (L j : ℕ) := ↥((Finset.univ : Finset (Fin L)).powersetCard j)

/-- The positions and letters recorded by a charged rectangle. -/
abbrev ChargedRectangle (L b t : ℕ) :=
  (j : Fin (t+1)) × (S : ChargedSupport L j.val) × (↥S.val → BitLetter b)

variable {L b t : ℕ}

/-- Both endpoints of a charged rectangle carry the same restriction. -/
def chargedEndpoint (R : ChargedRectangle L b t) : Set (BitLabel L b) :=
  {v | ∀ i : R.2.1.val, R.2.2 i = v i.val}

private def agreePositions (v w : BitLabel L b) : Finset (Fin L) :=
  Finset.univ.filter fun i => v i = w i

private theorem card_agreePositions (v w : BitLabel L b) :
    (agreePositions v w).card = L - routingDistance (bitLabelIndex L b v) (bitLabelIndex L b w) := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin L)))
    (fun i => v i = w i)
  have hd : (Finset.univ.filter fun i => v i ≠ w i).card =
      routingDistance (bitLabelIndex L b v) (bitLabelIndex L b w) := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    change (if v i ≠ w i then 1 else 0) = (if bitLetterIndex b (v i) = bitLetterIndex b (w i) then 0 else 1)
    simp [ite_not]
  rw [hd, Finset.card_univ, Fintype.card_fin] at h
  unfold agreePositions
  omega

private theorem sum_charged_data {A : Type*} [AddCommMonoid A]
    (u : A) (j : Fin (t+1)) (S : ChargedSupport L j.val) (v w : BitLabel L b) :
    (∑ a : ↥S.val → BitLetter b, if v ∈ chargedEndpoint (⟨j, S, a⟩ : ChargedRectangle L b t) ∧
      w ∈ chargedEndpoint (⟨j, S, a⟩ : ChargedRectangle L b t) then u else 0) =
    if S.val ⊆ agreePositions v w then u else 0 := by
  classical
  let av (i : S.val) := v i.val
  rw [Finset.sum_eq_single av]
  · have h : (v ∈ chargedEndpoint (⟨j, S, av⟩ : ChargedRectangle L b t) ∧
        w ∈ chargedEndpoint (⟨j, S, av⟩ : ChargedRectangle L b t)) ↔ S.val ⊆ agreePositions v w := by
      constructor
      · intro hp i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp.2 ⟨i, hi⟩⟩
      · intro hs
        exact ⟨fun _ => rfl, fun i => (Finset.mem_filter.mp (hs i.property)).2⟩
    simp only [h]
  · intro a _ hne
    exact ite_eq_right fun h => hne (funext h.1)
  · simp

/-- Weighted overlaps are binomial coefficients in the number of agreement positions. -/
theorem sum_chargedRectangle_weights {A : Type*} [Semiring A]
    (u : Fin (t+1) → A) (v w : BitLabel L b) :
    (∑ R : ChargedRectangle L b t,
      if v ∈ chargedEndpoint R ∧ w ∈ chargedEndpoint R then u R.1 else 0) =
    ∑ j : Fin (t+1),
      (((L - routingDistance (bitLabelIndex L b v) (bitLabelIndex L b w)).choose j.val : ℕ) : A) * u j := by
  classical
  simp only [Fintype.sum_sigma, sum_charged_data]
  apply Finset.sum_congr rfl
  intro j _
  let B := (Finset.univ : Finset (Fin L)).powersetCard j.val
  have hfilter : B.filter (· ⊆ agreePositions v w) = (agreePositions v w).powersetCard j.val := by
    ext S
    simp only [B, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      and_comm]
  change (∑ S : B, if S.val ⊆ agreePositions v w then u j else 0) = _
  rw [Finset.sum_coe_sort B (fun S => if S ⊆ agreePositions v w then u j else 0),
    ← Finset.sum_filter, hfilter, Finset.sum_const, Finset.card_powersetCard,
    card_agreePositions, nsmul_eq_mul]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
