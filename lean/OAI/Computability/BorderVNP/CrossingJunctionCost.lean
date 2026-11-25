import OAI.Computability.BorderVNP.CrossingJunctionSites

/-!
# Cost of a realized crossing network

The layout sum of Section 4.4 agrees with the edge-by-edge cost of the
network that implements its two cut factors and the opposite side tensor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

variable {D p : ℕ}

private noncomputable def edgeCost {P : Type*} {bits : P → ℕ}
    (N : Network D P bits) (e : N.Edge) : ℝ :=
  N.width e * dist (N.position (N.src e)) (N.position (N.dst e))

private theorem antipode_costs (m R : ℕ) (negative : Fin D → Bool) (I : Finset (Fin D ⊕ Fin p))
    (moveLeft : Bool) (z : EuclideanSpace ℝ (Fin D)) (hz : ‖z‖ ≤ 1) (i : Fin D) :
    (∑ sign : Bool, edgeCost (junctionNetwork m R negative I moveLeft z hz) (.inl (i,sign))) =
      m * (dist (-crossingTerminal negative i) 0 +
        if i ∈ (if moveLeft then I else Iᶜ).toLeft then dist (crossingTerminal negative i) z
        else dist (crossingTerminal negative i) 0) := by
  rw [Fintype.sum_bool]
  by_cases hi : Sum.inl i ∈ I <;> cases hn : negative i <;> cases moveLeft <;>
    simp [edgeCost, junctionNetwork, antipodalPosition, crossingTerminal, hi, hn] <;> ring

private theorem bridge_cost (m R : ℕ) (negative : Fin D → Bool) (I : Finset (Fin D ⊕ Fin p))
    (moveLeft : Bool) (z : EuclideanSpace ℝ (Fin D)) (hz : ‖z‖ ≤ 1) (j : Fin p) :
    edgeCost (junctionNetwork m R negative I moveLeft z hz) (.inr (.inl j)) =
      if j ∈ (if moveLeft then I else Iᶜ).toRight then m * dist z 0 else 0 := by
  by_cases hj : Sum.inr j ∈ I <;> cases moveLeft <;>
    simp [edgeCost, junctionNetwork, hj, dist_comm]

private theorem split_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f g : ι → ℝ) :
    (∑ i, if i ∈ S then f i else g i) = (∑ i ∈ S, f i) + ∑ i ∈ Sᶜ, g i := by
  rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sdiff_eq_filter]
  rfl

/-- The three-junction network charges exactly the physical layout cost, including
all rank bits, for either direction of displacement. -/
theorem junctionNetwork_cost (m R : ℕ) (negative : Fin D → Bool) (I : Finset (Fin D ⊕ Fin p))
    (moveLeft : Bool) (z : EuclideanSpace ℝ (Fin D)) (hz : ‖z‖ ≤ 1) :
    (junctionNetwork m R negative I moveLeft z hz).cost =
      layoutCost negative (if moveLeft then I else Iᶜ) z m (Nat.clog 2 R) := by
  let N := junctionNetwork m R negative I moveLeft z hz
  let S := if moveLeft then I else Iᶜ
  let f (e : (Fin D × Bool) ⊕ (Fin p ⊕ Unit)) := edgeCost N e
  change (∑ e, f e) = layoutCost negative S z _ _
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_unique (f := fun a : Unit ↦ f (.inr (.inr a)))]
  simp_rw [show ∀ i, (∑ sign : Bool, f (.inl (i,sign))) = _ from
    antipode_costs m R negative I moveLeft z hz]
  simp_rw [show ∀ j, f (.inr (.inl j)) = _ from bridge_cost m R negative I moveLeft z hz]
  have hr : f (.inr (.inr ())) = Nat.clog 2 R * dist z 0 := by
    cases moveLeft <;> simp [f, edgeCost, N, junctionNetwork, dist_comm]
  rw [hr, ← Finset.mul_sum, Finset.sum_add_distrib, split_sum, Finset.sum_ite_mem, Finset.univ_inter]
  unfold layoutCost
  simp only [← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
  dsimp only [S]
  ring

/-- A balanced cut yields a concrete network with the prescribed antipodal ports
and cost at most `2Dm − 0.002m`. The original cut stays fixed and only its moved
factor changes. -/
theorem exists_junctionNetwork_saving (negative : Fin D → Bool) (I : Finset (Fin D ⊕ Fin p))
    {m R : ℕ} (hD : 441 ≤ D) (hp : (p : ℝ) ≤ 21/20 * Real.sqrt D)
    (hlo : D + p ≤ 3 * I.card) (hhi : 3 * I.card ≤ 2 * (D + p))
    (hlarge : 100 ≤ (m : ℝ) * Real.sqrt D)
    (hrank : (R : ℝ) ≤ (2 : ℝ) ^ (1 / 50 * m * Real.sqrt D)) :
    ∃ (moveLeft : Bool) (z : EuclideanSpace ℝ (Fin D)) (hz : ‖z‖ ≤ 1),
      (junctionNetwork m R negative I moveLeft z hz).cost ≤ 2 * D * m - m/500 := by
  obtain ⟨S, hs, z, hz, hcost⟩ := balanced_layout_saving negative I hD hp hlo hhi hlarge hrank
  rcases hs with rfl | rfl
  · exact ⟨true, z, hz, (junctionNetwork_cost m R negative S true z hz).le.trans hcost⟩
  · exact ⟨false, z, hz, (junctionNetwork_cost m R negative I false z hz).le.trans hcost⟩

end Crossing

end BorderVNP
end Computability
end OAI
