import OAI.LinearAlgebra.SpectralBooks.SpectralSpace

/-! # Grouping local indices along a placement

A matrix acting at an occupied site is the tensor product of the matrices
on its preimages. This makes grouping monotone for arbitrary placements.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

open scoped Classical

/-- Regrouping a coordinate tuple over the fibers of a placement is a bijection. -/
def groupIndexEquiv {I J : Type*} (σ : I → J) (A : I → Type*) :
    (∀ i, A i) ≃ (∀ j, (t : {i // σ i = j}) → A t.1) :=
  Equiv.piCongrFiberwise (fun _ => Equiv.refl _)

@[simp] theorem groupIndexEquiv_apply {I J : Type*} (σ : I → J) (A : I → Type*)
    (a : ∀ i, A i) (j : J) (t : {i // σ i = j}) : groupIndexEquiv σ A a j t = a t.1 := rfl

@[simp] theorem groupIndexEquiv_symm_apply {I J : Type*} (σ : I → J) (A : I → Type*)
    (a : ∀ j, (t : {i // σ i = j}) → A t.1) (i : I) :
    (groupIndexEquiv σ A).symm a i = a (σ i) ⟨i, rfl⟩ := rfl

namespace Raw

variable {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]

/-- Grouped matrices are Kronecker products inside each fiber of the placement. -/
theorem group_restricts (σ : I → J) {X Y : Raw I K} (h : X.Restricts Y) :
    (X.group σ).Restricts (Y.group σ) := by
  classical
  obtain ⟨M, hM⟩ := h
  refine ⟨fun j b a => ∏ i : {i // σ i = j}, M i.1 (b i) (a i), fun x => ?_⟩
  change X.coeff ((groupIndexEquiv σ X.Leg).symm x) = _
  rw [hM]
  refine Fintype.sum_equiv (groupIndexEquiv σ Y.Leg) _ _ fun a => ?_
  apply congrArg (Y.coeff a * ·)
  let w (p : Σ j, {i // σ i = j}) := M p.2.1 (x p.1 p.2) (a p.2.1)
  calc
    _ = ∏ p, w p := Fintype.prod_equiv (Equiv.sigmaFiberEquiv σ).symm _ _ (fun i => rfl)
    _ = _ := Fintype.prod_sigma w

/-- Grouping commutes with the tensor product by collecting first and second coordinates. -/
theorem group_mul_equivalent (σ : I → J) (X Y : Raw I K) :
    ((X.mul Y).group σ).Equivalent ((X.group σ).mul (Y.group σ)) := by
  apply reindex_equivalent (fun j =>
    Equiv.arrowProdEquivProdArrow {i // σ i = j} (fun i => X.Leg i.1) (fun i => Y.Leg i.1))
  intro x
  rfl

/-- A grouped product of singleton bases still represents the scalar unit. -/
theorem group_one_equivalent (σ : I → J) :
    ((one I K).group σ).Equivalent (one J K) := by
  let (j : J) : Unique (((one I K).group σ).Leg j) := inferInstanceAs (Unique (∀ _ : {i // σ i = j}, PUnit))
  apply reindex_equivalent (fun _ => Equiv.equivPUnit _)
  intro x
  rfl

/-- A nonempty fiber contains an empty factor when every original leg is empty. -/
theorem group_zero_equivalent (σ : I → J) (hs : Function.Surjective σ) :
    ((zero I K).group σ).Equivalent (zero J K) := by
  classical
  have (j : J) : IsEmpty (((zero I K).group σ).Leg j) := by
    obtain ⟨i, hi⟩ := hs j
    exact ⟨fun x => (x ⟨i, hi⟩).elim⟩
  apply reindex_equivalent (fun _ => Equiv.equivPEmpty _)
  intro x
  rfl

end Raw
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
