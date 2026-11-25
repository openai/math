import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Ops

/-! # Diagonal tensors and their direct sums -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor.Raw

universe v
variable (I K : Type*) [Fintype I] [CommSemiring K]

/-- The common-label diagonal only depends on the label type up to equivalence. -/
theorem diagonal_equiv {α β : Type v} [Fintype α] [Fintype β] (e : α ≃ β) :
    (diagonal I K α).Equivalent (diagonal I K β) := by
  classical
  apply reindex_equivalent (fun _ => e)
  intro (x : I → α)
  simp only [diagonal]
  refine Fintype.sum_equiv e _ _ fun a => ?_
  have h : (fun i => e (x i)) = (fun _ => e a) ↔ x = (fun _ => a) := by
    simp [funext_iff]
  congr! 1
  exact h.symm

/-- The empty diagonal is the zero tensor. -/
theorem diagonal_empty_equivalent :
    (diagonal I K PEmpty.{v + 1}).Equivalent (zero I K) := by
  classical
  apply reindex_equivalent (fun _ => Equiv.refl _)
  intro x
  simp [diagonal]

/-- The one-label diagonal is the scalar unit. -/
theorem diagonal_unit_equivalent :
    (diagonal I K PUnit.{v + 1}).Equivalent (one I K) := by
  classical
  apply reindex_equivalent (X := diagonal I K _) (Y := one I K) (fun _ => Equiv.refl _)
  intro (x : I → PUnit.{v + 1})
  simp [diagonal, one, Subsingleton.elim x (fun _ => PUnit.unit)]

private theorem push_constant_labels (α : Type v) [Fintype α] {Y : Type*}
    (f : (I → α) → Y) (y : Y) :
    pushCoeff f (diagonal I K α).coeff y =
      ∑ a : α, if f (fun _ => a) = y then 1 else 0 := by
  classical
  let c (a : α) : I → α := fun _ => a
  have hc : (diagonal I K α).coeff = pushCoeff c (fun _ => 1) := by
    funext x
    apply Finset.sum_congr rfl
    intro a _
    change (if x = c a then (1 : K) else 0) = (if c a = x then 1 else 0)
    congr! 1
    exact eq_comm
  rw [hc, pushCoeff_comp]
  rfl

/-- A direct sum of diagonals has all the labels of the disjoint union. -/
theorem diagonal_sum_equivalent (α β : Type v) [Fintype α] [Fintype β] :
    ((diagonal I K α).add (diagonal I K β)).Equivalent (diagonal I K (α ⊕ β)) := by
  classical
  apply reindex_equivalent (X := (diagonal I K α).add (diagonal I K β))
    (Y := diagonal I K (α ⊕ β)) (fun _ => Equiv.refl _)
  intro (x : I → α ⊕ β)
  let f (y : I → α) (i : I) : α ⊕ β := Sum.inl (y i)
  let g (y : I → β) (i : I) : α ⊕ β := Sum.inr (y i)
  change pushCoeff f (diagonal I K α).coeff x +
    pushCoeff g (diagonal I K β).coeff x = (diagonal I K (α ⊕ β)).coeff x
  rw [push_constant_labels I K α, push_constant_labels I K β]
  simp only [diagonal, Fintype.sum_sum_type]
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intro a _ <;>
    congr! 1 <;> exact eq_comm

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
