import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Raw

/-! # Tensor classes ordered by restriction

Mutual restriction identifies precisely those tensors with the same upper and lower
bounds in the local restriction preorder.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v u w

/-- Finite site tensors up to mutual restriction. -/
def TensorClass (I : Type u) (K : Type w) [Fintype I] [CommSemiring K] :=
  Quotient (Raw.setoid.{v} I K)

variable {I : Type u} {K : Type w} [Fintype I] [CommSemiring K]

/-- Pass a coefficient tensor to its class under mutual restriction. -/
def ofRaw (X : Raw.{v} I K) : TensorClass.{v} I K :=
  Quotient.mk _ X

@[simp] theorem ofRaw_eq_iff {X Y : Raw.{v} I K} :
    ofRaw X = ofRaw Y ↔ X.Equivalent Y := Quotient.eq

instance : LE (TensorClass.{v} I K) where
  le := Quotient.lift₂ Raw.Restricts fun _ _ _ _ hX hY => propext
    ⟨fun h => restrict_trans hX.2 (restrict_trans h hY.1),
     fun h => restrict_trans hX.1 (restrict_trans h hY.2)⟩

@[simp] theorem ofRaw_le_iff {X Y : Raw.{v} I K} :
    ofRaw X ≤ ofRaw Y ↔ X.Restricts Y := Iff.rfl

instance : PartialOrder (TensorClass.{v} I K) where
  le_refl X := Quotient.inductionOn X fun x => restrict_refl x.coeff
  le_trans X Y Z := Quotient.inductionOn₃ X Y Z fun _ _ _ => restrict_trans
  le_antisymm X Y := Quotient.inductionOn₂ X Y fun _ _ h g => Quotient.sound ⟨h, g⟩

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
