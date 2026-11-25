import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Raw

/-! # Multiplication laws for finite tensors up to mutual restriction -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

variable {I K : Type*} [Fintype I] [CommSemiring K]

/-- The tensor product is associative after relabeling the paired bases. -/
theorem mul_assoc_equivalent (X Y Z : Raw I K) :
    ((X.mul Y).mul Z).Equivalent (X.mul (Y.mul Z)) := by
  apply reindex_equivalent (fun _ => Equiv.prodAssoc _ _ _)
  intro x
  apply mul_assoc

/-- Swapping the local product factors commutes the tensor product. -/
theorem mul_comm_equivalent (X Y : Raw I K) :
    (X.mul Y).Equivalent (Y.mul X) := by
  apply reindex_equivalent (fun _ => Equiv.prodComm _ _)
  intro x
  apply mul_comm

/-- Dropping the singleton basis index identifies a unit product with its other factor. -/
theorem one_mul_equivalent (X : Raw I K) : ((one I K).mul X).Equivalent X := by
  apply reindex_equivalent (fun _ => Equiv.punitProd _)
  intro x
  apply one_mul

/-- Tensoring with the empty tensor gives an empty basis at each site. -/
theorem zero_mul_equivalent [Nonempty I] (X : Raw I K) :
    ((zero I K).mul X).Equivalent (zero I K) := by
  apply reindex_equivalent (fun _ => Equiv.pemptyProd _)
  intro x
  exact (x (Classical.arbitrary I)).1.elim

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
