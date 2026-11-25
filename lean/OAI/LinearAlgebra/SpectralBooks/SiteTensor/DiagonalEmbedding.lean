import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Raw

/-! # Embedding the labels of a diagonal tensor -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor.Raw

universe u v w

variable (I : Type u) (K : Type w) [Fintype I] [Nonempty I] [CommSemiring K]
variable {α β : Type v} [Fintype α] [Fintype β]

/-- Coordinate projections at every site restrict a diagonal to an embedded label set. -/
theorem diagonal_restricts_of_embedding (e : α ↪ β) :
    (diagonal I K α).Restricts (diagonal I K β) := by
  classical
  unfold Restricts diagonal
  refine ⟨fun _ a b => if b = e a then 1 else 0, fun x => ?_⟩
  simp_rw [Fintype.prod_boole]
  have heq (y : I → β) : (∀ i, y i = e (x i)) ↔ y = fun i => e (x i) :=
    funext_iff.symm
  simp only [heq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  let i₀ : I := Classical.choice inferInstance
  rw [Finset.sum_eq_single (x i₀), Finset.sum_eq_single (e (x i₀))]
  · simp [funext_iff]
  · intro b _ hb
    exact ite_eq_right fun h => (hb (congrFun h i₀).symm).elim
  · simp
  · intro a _ ha
    exact ite_eq_right fun h => (ha (congrFun h i₀).symm).elim
  · simp

/-- A larger diagonal restricts to every diagonal with at most as many labels. -/
theorem diagonal_restricts_of_card_le (h : Fintype.card α ≤ Fintype.card β) :
    (diagonal I K α).Restricts (diagonal I K β) := by
  apply diagonal_restricts_of_embedding
  exact (Fintype.equivFin α).toEmbedding.trans
    ((Fin.castLEEmb h).trans (Fintype.equivFin β).symm.toEmbedding)

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
