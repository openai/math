import OAI.Computability.BorderVNP.CrossingJunctionCost

/-!
# The finite collection of layouts for the border identity

An index specifies an orientation of the antipodal pairs and a balanced
group cut. The geometry is chosen once for each index and is independent
of the table entries at the approximating points.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

variable {D p : ℕ}

/-- Group cuts for which both sides contain between one third and two thirds of the groups. -/
def balancedCuts (D p : ℕ) : Finset (Finset (Fin D ⊕ Fin p)) :=
  Finset.univ.filter fun I ↦ D + p ≤ 3 * I.card ∧ 3 * I.card ≤ 2 * (D + p)

/-- Number of layouts after choosing the crossing orientations and balanced cut. -/
abbrev LayoutIndex (D p : ℕ) := (Fin D → Bool) × ↥(balancedCuts D p)

/-- There are at most `2^(D+ℓ)` networks in the sum, where `ℓ=D+p`. -/
theorem card_layoutIndex_le (D p : ℕ) : Fintype.card (LayoutIndex D p) ≤ 2 ^ (D + (D + p)) := by
  have h : (balancedCuts D p).card ≤ 2 ^ (D + p) := by
    simpa [Fintype.card_sum] using (balancedCuts D p).card_le_univ
  simp only [LayoutIndex, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_coe, pow_add 2 D (D + p)]
  exact Nat.mul_le_mul_left _ h

/-- When there are at least two groups a cut of half their number is balanced. -/
theorem card_layoutIndex_pos (h : 2 ≤ D + p) : 0 < Fintype.card (LayoutIndex D p) := by
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin D ⊕ Fin p))) (n := (D + p)/2)
    (by simp [Fintype.card_sum]; omega)
  have hs : S ∈ balancedCuts D p := by simp [balancedCuts, hS]; omega
  exact Fintype.card_pos_iff.mpr ⟨(fun _ ↦ false, ⟨S, hs⟩)⟩

/-- Geometry data for each network of a fixed fused crossing. -/
structure BalancedPlacements (D p : ℕ) where
  /-- Which of the two cut factors is displaced. -/
  moved : LayoutIndex D p → Bool
  /-- Junction positions in the same Euclidean coordinate system as the external ports. -/
  point : LayoutIndex D p → EuclideanSpace ℝ (Fin D)
  in_ball : ∀ i, ‖point i‖ ≤ 1

/-- Assemble the previously chosen network at an index. -/
noncomputable def BalancedPlacements.net (g : BalancedPlacements D p) (m R : ℕ)
    (i : LayoutIndex D p) : Network D (Fin D × Bool) (fun _ ↦ m) :=
  junctionNetwork m R i.1 i.2.val (g.moved i) (g.point i) (g.in_ball i)

/-- Geometry exists simultaneously for all terms, using the same width bound. -/
theorem exists_balancedPlacements {m R : ℕ} (hD : 441 ≤ D)
    (hp : (p : ℝ) ≤ 21/20 * Real.sqrt D) (hlarge : 100 ≤ (m : ℝ) * Real.sqrt D)
    (hrank : (R : ℝ) ≤ (2 : ℝ) ^ (1/50 * m * Real.sqrt D)) :
    ∃ g : BalancedPlacements D p, ∀ i, (g.net m R i).cost ≤ 2 * D * m - m/500 := by
  have h (i : LayoutIndex D p) := exists_junctionNetwork_saving i.1 i.2.val hD hp
    (Finset.mem_filter.mp i.2.property).2.1 (Finset.mem_filter.mp i.2.property).2.2 hlarge hrank
  choose moved z hz hc using h
  exact ⟨⟨moved, z, hz⟩, hc⟩

end Crossing

end BorderVNP
end Computability
end OAI
