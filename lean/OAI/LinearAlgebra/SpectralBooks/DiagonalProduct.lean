import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Raw

/-! # Restriction and multiplication of common-label diagonals -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

open scoped BigOperators Classical

universe v
variable {I K : Type*} {α β : Type v} [Fintype I] [CommSemiring K]

namespace Raw

/-- A diagonal coefficient is one when all sites agree with the fixed site. -/
theorem diagonal_coeff_at (i₀ : I) [Fintype α] (x : I → α) :
    (diagonal I K α).coeff x = if ∀ i, x i = x i₀ then 1 else 0 := by
  classical
  simp only [diagonal]
  rw [Finset.sum_eq_single (x i₀)]
  · simp [funext_iff]
  · intro b _ hb
    apply ite_eq_right
    intro hx
    exact hb (congrFun hx i₀).symm
  · simp

/-- Tensor multiplication pairs the two independent common labels. -/
theorem diagonal_product_equivalent [Nonempty I] [Fintype α] [Fintype β] :
    ((diagonal I K α).mul (diagonal I K β)).Equivalent (diagonal I K (α × β)) := by
  classical
  let i₀ : I := Classical.choice inferInstance
  apply reindex_equivalent (X := (diagonal I K α).mul (diagonal I K β))
    (Y := diagonal I K (α × β)) (fun _ => Equiv.refl _)
  intro (x : I → α × β)
  change (diagonal I K α).coeff (fun i => (x i).1) *
    (diagonal I K β).coeff (fun i => (x i).2) = (diagonal I K (α × β)).coeff x
  simp only [diagonal_coeff_at i₀, Prod.ext_iff, forall_and,
    ← ite_and, ite_mul, one_mul, zero_mul]

end Raw
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
