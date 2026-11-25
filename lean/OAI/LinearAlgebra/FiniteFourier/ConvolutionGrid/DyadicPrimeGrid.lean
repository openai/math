import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPrimeAxis
import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoGridProduct

/-! # Multiplication on a dyadic prime grid

Tensor the prime-axis transforms after scalar extension and recover the entire
cyclic product from the binomial product on each active subset.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace ConvolutionGrid

open Matrix Deformation
open scoped BigOperators Classical

variable {O R σ : Type*} [CommRing O] [Nontrivial O] [CommRing R] [Fintype σ]
  {p : σ → ℕ} [∀ i, Fact (p i).Prime] {C : ∀ i, PrimeAxisOrbit (p i)} {u : σ → Oˣ}
  {hm : ∀ i, IsUnit ((p i-1 : ℕ) : O)}
  (a : ∀ i, DyadicPrimeAxis O (p i) (C i) (u i) (hm i)) (φ : O →+* R)

local notation "sector" => sectorIndex (K := fun i : σ => Fin (p i-1))

/-- The tensor of the scalar-extended transforms sends a cyclic product to
the wrapped product on every active subset, with the binomials defined over the base. -/
theorem dyadic_grid_sector (S : Finset σ) (x y : (∀ i, ZMod (p i)) → R) :
    let F := columns (fun i => (a i).forward.map φ)
    (F *ᵥ cyclicProduct x y) ∘ sector S =
      multiply (Dyadic.coeff (fun i : S => φ ((a i.val).beta : O)) (fun i : S => p i.val-1))
        ((F *ᵥ x) ∘ sector S) ((F *ᵥ y) ∘ sector S) := by
  let A := fun i => (a i).forward.map φ
  let c := fun i => Dyadic.axisCoeff (m := p i-1) (φ ((a i).beta:O))
  have h₀ (i : σ) (g t : ZMod (p i)) : A i none (g+t) = A i none g * A i none t :=
    (a i).map_forward_add_none φ g t
  have h₁ (i : σ) (g t : ZMod (p i)) (k : Fin (p i-1)) :
      A i (some k) (g+t) = multiply (c i) (fun j => A i (some j) g)
        (fun j => A i (some j) t) k := (a i).map_forward_add_some φ g t k
  have h := sector_cyclicProduct (K := fun i => Fin (p i-1)) (G := fun i => ZMod (p i))
    S A c h₀ h₁ x y
  have hc : coeff (fun i : S => c i.val) =
      Dyadic.coeff (fun i : S => φ ((a i.val).beta:O)) (fun i : S => p i.val-1) := rfl
  rw [hc] at h
  exact h

/-- Inverting the mapped tensor transform reads the cyclic product from its sectors. -/
theorem dyadic_grid_recover (x y : (∀ i, ZMod (p i)) → R)
    (z : (∀ i, Option (Fin (p i-1))) → R)
    (hz : ∀ S : Finset σ, z ∘ sector S =
      multiply (Dyadic.coeff (fun i : S => φ ((a i.val).beta : O)) (fun i : S => p i.val-1))
        ((columns (fun i => (a i).forward.map φ) *ᵥ x) ∘ sector S)
        ((columns (fun i => (a i).forward.map φ) *ᵥ y) ∘ sector S)) :
    columns (fun i => (a i).backward.map φ) *ᵥ z = cyclicProduct x y := by
  have he : z = columns (fun i => (a i).forward.map φ) *ᵥ cyclicProduct x y := by
    funext j
    obtain ⟨⟨s,k⟩,rfl⟩ := sectorEquiv.surjective j
    exact congrFun ((hz s).trans (dyadic_grid_sector a φ s x y).symm) k
  rw [he, mulVec_mulVec, columns_mul]
  simp only [DyadicPrimeAxis.map_backward_mul_forward, columns_identity, one_mulVec]

end ConvolutionGrid

end FiniteFourier
end LinearAlgebra
end OAI
