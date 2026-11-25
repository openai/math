import OAI.ThreeFlat.CrossingBudget

namespace OAI
/-! # Exact wire budgets for a word of crossing tiles and a remainder -/

namespace ThreeFlat.CrossingSupply

open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators

noncomputable section

private theorem slack_add (u v : ℕ) : slack (u + v) = slack u + slack v := by
  simp only [slack, wire, Finsupp.single_add]
  ac_rfl

theorem tiled_supply_budgets (q R b t r L : ℕ) (hR : 2 ≤ R)
    (n : Fin L → SupplyChoice → ℕ) (hn : ∀ l, ∑ j, n l j = b) (w : Fin t → Fin L) :
    ∃ u v : ℕ, ∃ H : Widths 6,
      u + v = 4*q*b*t ∧
      (∀ e : Chord 6, ¬ (e.1.1 < 4 ∧ 4 ≤ e.1.2) → H e = 0) ∧
      load 4 H = (4*q*b*t+r)*R ∧ load 5 H = (4*q*b*t+r)*R ∧
      (∑ i, ∑ j, n (w i) j • supply q R j) + (slack r + arms 0 (r*R) (r*R)) =
        matching true u + matching false v + slack (2*b*t+r) + H := by
  classical
  let a (j : SupplyChoice) := ∑ i, n (w i) j
  have ha : ∑ j, a j = b*t := by
    unfold a
    rw [Finset.sum_comm]
    simp [hn, Nat.mul_comm]
  have flatten : (∑ i, ∑ j, n (w i) j • supply q R j) = ∑ j, a j • supply q R j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_smul.symm
  obtain ⟨u, v, huv, hg, h4, h5⟩ := aggregate_supply_budgets q R hR a ha
  rw [hg, map_add, side_load 4 le_rfl, zero_add] at h4
  rw [hg, map_add, side_load 5 (by decide), zero_add] at h5
  let g := arms 0 (r*R) (r*R)
  refine ⟨u, v, pooledArms q R a + g, by simpa only [Nat.mul_assoc] using huv, ?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [g, Finsupp.add_apply, pooledArms_supported q R a e he,
      arms_supported 0 _ _ e he, zero_add]
  · rw [map_add, h4]
    have h : load 4 g = r*R := by norm_num [g, arms, site]
    rw [h]
    ring
  · rw [map_add, h5]
    have h : load 5 g = r*R := by norm_num [g, arms, site]
    rw [h]
    ring
  · rw [flatten, hg, slack_add, Nat.mul_assoc 2 b t]
    change _ + (slack r + g) = _
    ac_rfl

end
end ThreeFlat.CrossingSupply

end OAI
