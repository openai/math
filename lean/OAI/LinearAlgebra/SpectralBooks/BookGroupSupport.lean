import OAI.LinearAlgebra.SpectralBooks.BookFiber
import OAI.LinearAlgebra.SpectralBooks.TrivialSlots

/-! # Grouping a tensor inside its set of occupied sites -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

variable {I S : Type} {K : Type*} [Fintype I] [Fintype S] [CommSemiring K]

private def supportFiber (σ : I → S) (A : I → Type) (O : Type) (s : S) :
    ((k : {i // (Sum.inl (σ i) : S ⊕ O) = Sum.inl s}) → A k.val) ≃
      ((k : {i // σ i = s}) → A k.val) where
  toFun f k := f ⟨k.val, congrArg Sum.inl k.property⟩
  invFun f k := f ⟨k.val, Sum.inl.inj k.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Grouping into a summand of the entire site set gives the grouped tensor
on that summand with a one-dimensional slot at every other site. -/
theorem group_support_equivalent (T : Raw.{0} I K) (σ : I → S) (O : Type) [Fintype O] :
    (T.group (fun i => (Sum.inl (σ i) : S ⊕ O))).Equivalent (withTrivial O (T.group σ)) := by
  let e (j : S ⊕ O) : (T.group (fun i => (Sum.inl (σ i) : S ⊕ O))).Leg j ≃
      (withTrivial O (T.group σ)).Leg j := match j with
    | .inl s => supportFiber σ T.Leg O s
    | .inr o => fiberEmptyEquiv (fun i => (Sum.inl (σ i) : S ⊕ O)) T.Leg (.inr o) (fun _ => Sum.inl_ne_inr)
  exact reindex_equivalent e (fun _ => rfl)

/-- Placing the sites by inclusion into a larger set is equivalent to
extending the original tensor by trivial slots. -/
theorem group_inl_equivalent (T : Raw.{0} S K) (O : Type) [Fintype O] :
    (T.group (Sum.inl : S → S ⊕ O)).Equivalent (withTrivial O T) := by
  let e (j : S ⊕ O) : (T.group (Sum.inl : S → S ⊕ O)).Leg j ≃
      (withTrivial O T).Leg j := match j with
    | .inl s => fiberAtEquiv (Sum.inl : S → S ⊕ O) T.Leg s (fun _ => Sum.inl.inj)
    | .inr o => fiberEmptyEquiv (Sum.inl : S → S ⊕ O) T.Leg (.inr o) (fun _ => Sum.inl_ne_inr)
  exact reindex_equivalent e (fun _ => rfl)

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
