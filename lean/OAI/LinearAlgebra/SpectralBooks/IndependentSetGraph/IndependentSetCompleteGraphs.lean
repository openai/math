import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.IndependentSetChoices
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.IndependentSetTours
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.IndependentSetSubcubicProjection

/-! # Bipartite subcubic projections for finite tables and Hamiltonian cycle -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace IndependentSetGraph
open scoped Classical BigOperators
noncomputable section

/-- Every finite table of signed, weighted local choices projects from a bipartite
subcubic independent-set polynomial at each sufficiently large size. -/
theorem exists_gridProjection_of_choices {R σ I : Type*} [CommRing R] {A : I → Type*}
    [Fintype I] [∀ i, Fintype (A i)] (conflict : Sigma A → Sigma A → Prop)
    (w : Sigma A → ProjectionAtom R σ) {N : ℕ}
    (hN : Fintype.card (Sigma A) + Fintype.card I +
      25 * (Fintype.card (Sigma A)^2 + Fintype.card (Sigma A)) ≤ N) :
    Nonempty (GridProjection R σ (∑ s : ∀ i, A i, if compatibleSelector conflict s then
      ∏ i, atomPolynomial (w ⟨i,s i⟩) else 0) N) := by
  have hsize : Fintype.card (ChoiceVertex A) + 25 * Fintype.card (ChoiceEdge conflict) ≤ N := by
    rw [choice_vertex_card]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left 25 (choice_edge_card_le conflict)) _).trans hN
  obtain ⟨G⟩ := exists_gridProjection_of_polynomial (R := R) (choiceLeft conflict) (choiceRight conflict) hsize
  rw [← choice_projection conflict w]
  exact ⟨G.project (markedProjection w)⟩

/-- The ordinary directed Hamiltonian-cycle polynomial projects from a
bipartite subcubic independent-set polynomial at every size above this bound. -/
theorem exists_gridProjection_of_hamiltonian (R : Type*) [CommRing R] {m N : ℕ}
    (hm : 2 ≤ m) (hN : m^3 + m + 25 * (m^6 + m^3) ≤ N) :
    Nonempty (GridProjection R (Fin m × Fin m) (hamiltonianCyclePolynomial R m) N) := by
  let : NeZero m := ⟨by omega⟩
  have hsize : Fintype.card (TourVertex m) + 25 * Fintype.card (TourEdge m) ≤ N :=
    (Nat.add_le_add (tour_vertex_card_le m) (Nat.mul_le_mul_left 25 (tour_edge_card_le m))).trans hN
  obtain ⟨G⟩ := exists_gridProjection_of_polynomial (R := R) (tourLeft m) (tourRight m) hsize
  rw [← tour_projection R hm]
  exact ⟨G.project (tourProjection R m)⟩

end
end IndependentSetGraph

end SpectralBooks
end LinearAlgebra
end OAI
