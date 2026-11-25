import OAI.Computability.BorderVNP.CrossingGeometry
import OAI.Computability.BorderVNP.CrossingBudget
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum

/-!
# A shortening layout for each balanced summand

The side containing the selected junction is a subset of the disjoint union of the
terminal and bridge indices. The wire length below counts both antipodes separately,
the crossing bridges incident to the moved junction, and the rank cable.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

variable {D p : ℕ}

/-- Terminal on the first side of a crossing with the prescribed orientation. Its
partner on the opposite side is the negative vector. -/
noncomputable def crossingTerminal (negative : Fin D → Bool) (i : Fin D) :
    EuclideanSpace ℝ (Fin D) :=
  if negative i then -EuclideanSpace.single i 1 else EuclideanSpace.single i 1

private theorem norm_crossingTerminal (negative : Fin D → Bool) (i : Fin D) :
    ‖crossingTerminal negative i‖ = 1 := by
  exact (orthonormal_signed_terminals (Function.Embedding.refl (Fin D)) negative).1 i

/-- Wire cost for a junction displaced to `z`. All other junctions are at the origin. -/
noncomputable def layoutCost (negative : Fin D → Bool) (I : Finset (Fin D ⊕ Fin p))
    (z : EuclideanSpace ℝ (Fin D)) (m rankWidth : ℝ) : ℝ :=
  m * ((∑ i, dist (-crossingTerminal negative i) 0) +
    (∑ i ∈ I.toLeftᶜ, dist (crossingTerminal negative i) 0) +
    ∑ i ∈ I.toLeft, dist (crossingTerminal negative i) z) +
    m * (∑ _ ∈ I.toRight, dist z 0) + rankWidth * dist z 0

private theorem layout_favorable_side (negative : Fin D → Bool) (I : Finset (Fin D ⊕ Fin p))
    (hD : 0 < D) {m rankWidth : ℝ} (hm : 0 ≤ m)
    (hgap : 1/10 * Real.sqrt D ≤ Real.sqrt I.toLeft.card - I.toRight.card)
    (hrank : rankWidth ≤ 3/100 * m * Real.sqrt D) :
    ∃ z : EuclideanSpace ℝ (Fin D), ‖z‖ ≤ 1 ∧ layoutCost negative I z m rankWidth ≤ 2 * D * m - m/500 := by
  let e := I.toLeft.orderIsoOfFin rfl
  let axis := e.toEquiv.toEmbedding.trans (Function.Embedding.subtype _)
  let u (i : Fin I.toLeft.card) := crossingTerminal negative (axis i)
  have hu : Orthonormal ℝ u := orthonormal_signed_terminals axis (negative ∘ axis)
  have hsD : I.toLeft.card ≤ D := by simpa using I.toLeft.card_le_univ
  have hs : 0 < I.toLeft.card := by
    by_contra! hn
    rw [show I.toLeft.card = 0 by omega, Nat.cast_zero, Real.sqrt_zero] at hgap
    have : 0 < Real.sqrt D := Real.sqrt_pos.mpr (by exact_mod_cast hD)
    linarith [Nat.cast_nonneg (α := ℝ) I.toRight.card]
  let t : ℝ := 1 / (25 * Real.sqrt D)
  let z := t • junctionDirection u
  refine ⟨z, ?_, ?_⟩
  · have hd : 1 ≤ Real.sqrt D := by
      exact (Real.sqrt_one ▸ Real.sqrt_le_sqrt (show (1 : ℝ) ≤ D by exact_mod_cast hD))
    rw [show z = t • junctionDirection u from rfl, norm_smul, norm_junctionDirection u hu hs,
      Real.norm_eq_abs, abs_of_nonneg (by dsimp [t]; positivity), mul_one]
    exact (div_le_one (by positivity : 0 < 25 * Real.sqrt D)).mpr (by linarith)
  have hsave := displacedCost_le u hu hs hsD (b := I.toRight.card) hm (show Real.sqrt D / 10 ≤ _ by linarith) hrank
  have hsum : ∑ i ∈ I.toLeft, dist (crossingTerminal negative i) z = ∑ i, dist (u i) z := by
    rw [← Finset.sum_coe_sort]
    exact (e.toEquiv.sum_comp fun i ↦ dist (crossingTerminal negative i) z).symm
  have hc : ((I.toLeftᶜ.card : ℕ) : ℝ) = (D : ℝ) - I.toLeft.card := by
    simp [Finset.card_compl, Nat.cast_sub hsD]
  calc
    _ = displacedCost D u m I.toRight.card rankWidth t := by
      unfold layoutCost displacedCost
      rw [hsum]
      simp only [dist_zero_right, norm_neg, norm_crossingTerminal, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hc]
      change _ = (2 * D - I.toLeft.card) * m + m * (∑ i, dist (u i) z) + _ * ‖z‖
      ring
    _ ≤ _ := hsave

/-- For every balanced group cut in a crossing summand, one of the two groups can be
moved so that the complete layout saves `m/500` in wire length. Its rank cable
uses the integer number of bits needed to encode `R` possible states. -/
theorem balanced_layout_saving (negative : Fin D → Bool) (I : Finset (Fin D ⊕ Fin p))
    {m R : ℕ} (hD : 441 ≤ D) (hp : (p : ℝ) ≤ 21/20 * Real.sqrt D)
    (hlo : D + p ≤ 3 * I.card) (hhi : 3 * I.card ≤ 2 * (D + p))
    (hlarge : 100 ≤ (m : ℝ) * Real.sqrt D)
    (hrank : (R : ℝ) ≤ (2 : ℝ) ^ (1 / 50 * m * Real.sqrt D)) :
    ∃ S : Finset (Fin D ⊕ Fin p), (S = I ∨ S = Iᶜ) ∧
      ∃ z : EuclideanSpace ℝ (Fin D), ‖z‖ ≤ 1 ∧ layoutCost negative S z m (Nat.clog 2 R) ≤
        2 * D * m - m/500 := by
  have hs : I.toLeft.card ≤ D := by simpa using I.toLeft.card_le_univ
  have hb : I.toRight.card ≤ p := by simpa using I.toRight.card_le_univ
  have hnum := balanced_cut_side hD hp hs hb
    (I.card_toLeft_add_card_toRight ▸ hlo) (I.card_toLeft_add_card_toRight ▸ hhi)
  have hwidth := rankBits_le hlarge hrank
  rcases hnum with h | h
  · exact ⟨I, Or.inl rfl, layout_favorable_side negative I (by omega) (Nat.cast_nonneg m) h hwidth⟩
  · have hl : Iᶜ.toLeft = I.toLeftᶜ := by ext i; simp
    have hr : Iᶜ.toRight = I.toRightᶜ := by ext i; simp
    rw [← show Iᶜ.toLeft.card = D - I.toLeft.card by simp [hl, Finset.card_compl],
      ← show Iᶜ.toRight.card = p - I.toRight.card by simp [hr, Finset.card_compl]] at h
    exact ⟨Iᶜ, Or.inr rfl, layout_favorable_side negative Iᶜ (by omega) (Nat.cast_nonneg m) h hwidth⟩

end Crossing

end BorderVNP
end Computability
end OAI
