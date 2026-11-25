import OAI.LinearAlgebra.SpectralBooks.SpectralSpace

/-! # Local coordinates in singleton and empty placement fibers -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- Reading the unique occupied tensor coordinate in a placement fiber. -/
def fiberAtEquiv {I J : Type} (σ : I → J) (A : I → Type) (i : I)
    (h : ∀ k, σ k = σ i → k = i) : ((k : {k // σ k = σ i}) → A k.val) ≃ A i where
  toFun f := f ⟨i, rfl⟩
  invFun x k := (h k.val k.property).symm ▸ x
  left_inv f := by
    funext ⟨k, hk⟩
    obtain rfl := h k hk
    rfl
  right_inv _ := rfl

/-- A tensor with an empty placement fiber has a one-dimensional leg there. -/
def fiberEmptyEquiv {I J : Type} (σ : I → J) (A : I → Type) (j : J)
    (h : ∀ i, σ i ≠ j) : ((k : {k // σ k = j}) → A k.val) ≃ Unit where
  toFun _ := ()
  invFun _ k := (h k.val k.property).elim
  left_inv _ := funext fun k => (h k.val k.property).elim
  right_inv _ := rfl

end SpectralBooks
end LinearAlgebra
end OAI
