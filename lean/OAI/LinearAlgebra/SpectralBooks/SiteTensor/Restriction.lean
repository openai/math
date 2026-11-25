import OAI.LinearAlgebra.SpectralBooks.Crossing

/-!
# Composition and reindexing of tensor restrictions
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

open Crossing

variable {I : Type*} [Fintype I] {F : Type*} [CommSemiring F]
variable {A B C : I → Type*} [∀ i, Fintype (A i)]

/-- Relabeling the coordinate basis at each site gives a restriction. -/
theorem restrict_of_equiv {X : (∀ i, B i) → F} {Y : (∀ i, A i) → F}
    (e : ∀ i, B i ≃ A i) (h : ∀ x, X x = Y (fun i => e i (x i))) :
    IsRestriction X Y := by
  classical
  refine ⟨fun i b a => if a = e i b then 1 else 0, fun x => ?_⟩
  rw [h x]
  simp_rw [Fintype.prod_boole]
  have heq (a : ∀ i, A i) : (∀ i, a i = e i (x i)) ↔ a = fun i => e i (x i) :=
    funext_iff.symm
  simp [heq, mul_ite]

/-- Identity matrices give the reflexive restriction. -/
theorem restrict_refl (X : (∀ i, A i) → F) : IsRestriction X X :=
  restrict_of_equiv (fun i => Equiv.refl (A i)) fun _ => rfl

/-- Local matrix multiplication composes two restrictions. -/
theorem restrict_trans [∀ i, Fintype (B i)] {X : (∀ i, C i) → F}
    {Y : (∀ i, B i) → F} {Z : (∀ i, A i) → F}
    (hXY : IsRestriction X Y) (hYZ : IsRestriction Y Z) : IsRestriction X Z := by
  classical
  obtain ⟨M, hM⟩ := hXY
  obtain ⟨N, hN⟩ := hYZ
  refine ⟨fun i c a => ∑ b, N i b a * M i c b, fun x => ?_⟩
  rw [hM x]
  simp_rw [hN, Finset.sum_mul, Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib,
    mul_assoc]
  exact Finset.sum_comm

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
