import OAI.LinearAlgebra.SpectralBooks.Crossing

/-!
# Products preserve tensor restriction

The site matrices for two restrictions act on paired basis indices by their
Kronecker products.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

variable {I F : Type*} [Fintype I] [CommSemiring F]
  {A B C D : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

/-- The tensor product of two local restrictions is a local restriction. -/
theorem restrict_product
    {X : (∀ i, A i) → F} {Y : (∀ i, B i) → F}
    {X' : (∀ i, C i) → F} {Y' : (∀ i, D i) → F}
    (hX : Crossing.IsRestriction X' X) (hY : Crossing.IsRestriction Y' Y) :
    Crossing.IsRestriction
      (fun a : ∀ i, C i × D i => X' (fun i => (a i).1) * Y' (fun i => (a i).2))
      (fun a : ∀ i, A i × B i => X (fun i => (a i).1) * Y (fun i => (a i).2)) := by
  classical
  obtain ⟨M, hM⟩ := hX
  obtain ⟨N, hN⟩ := hY
  refine ⟨fun i x a => M i x.1 a.1 * N i x.2 a.2, fun x => ?_⟩
  dsimp
  rw [hM, hN, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow I A B).symm _ _ fun a => ?_
  simp only [Finset.prod_mul_distrib]
  ac_rfl

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
