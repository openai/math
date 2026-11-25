import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Raw
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Product
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.SumDef

/-! # Direct sum of finite coefficient tensors -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

universe v u w

variable {I : Type u} {K : Type w} [Fintype I]

/-- The direct sum uses a disjoint union at every site. -/
noncomputable def add [AddCommMonoid K] (X Y : Raw.{v} I K) : Raw.{v} I K :=
  ⟨fun i => X.Leg i ⊕ Y.Leg i, fun _ => inferInstance, sumCoeff X.coeff Y.coeff⟩

/-- Tensoring the local restricting maps restricts a product. -/
theorem mul_restricts [CommSemiring K] {X Y U V : Raw.{v} I K}
    (h : X.Restricts Y) (h' : U.Restricts V) : (X.mul U).Restricts (Y.mul V) :=
  restrict_product h h'

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
