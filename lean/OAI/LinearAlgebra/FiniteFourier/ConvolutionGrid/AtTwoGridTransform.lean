import OAI.LinearAlgebra.FiniteFourier.ConvolutionGrid.AtTwoGridProduct
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeAxis

/-! # Prime-grid multiplication in the integral deformation

The tensor change of basis on prime addresses decomposes their cyclic
convolution into the undeformed product table on each subset of active axes.
Reassembly uses the inverse tensor change of basis.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace ConvolutionGrid


open Matrix Deformation Polynomial
open scoped BigOperators Classical

variable {R σ : Type*} [CommRing R] [Fintype σ]

local notation "O₂" => CyclotomicCoefficients TwoLocalQuadratic
variable {M : ℕ} {p : σ → ℕ} [∀ i, Fact (p i).Prime] {hM : Odd M}
  {hp : ∀ i, p i % 4 = 3} {h7 : ∀ i, 7 ≤ p i}
  (a : ∀ i, AtTwoPrimeAxis M (p i) hM (hp i) (h7 i))
  (φ : O₂ M →+* R)

local notation "mₚ" => fun i : σ => (p i - 1) / 2
local notation "ρₚ" => fun i : σ => (((p i + 1) / 4 : ℕ) : O₂ M)
local notation "sector" => sectorIndex (K := fun i : σ => Fin 2 × Fin (mₚ i))

/-- The columns restricted to one active sector give exactly the original
quadratic-binomial product table after extending to any jet. -/
theorem atTwo_grid_sector (S : Finset σ) (x y : (∀ i, ZMod (p i)) → R) :
    let F := columns (fun i => (a i).forward.map φ)
    (F *ᵥ cyclicProduct x y) ∘ sector S =
      multiply (coeff (fun i : S => primeAxisActiveCoeff (m := mₚ i.val)
          (φ (ρₚ i.val)) (φ ((a i.val).beta))))
        ((F *ᵥ x) ∘ sector S) ((F *ᵥ y) ∘ sector S) := by
  let A := fun i => (a i).forward.map φ
  let c := fun i => primeAxisActiveCoeff (m := mₚ i) (φ (ρₚ i)) (φ (a i).beta)
  have h₀ (i : σ) (g t : ZMod (p i)) : A i none (g+t) = A i none g * A i none t := by
    simp only [A, AtTwoPrimeAxis.map_forward_none, mul_one]
  have h₁ (i : σ) (g t : ZMod (p i)) (k : Fin 2 × Fin (mₚ i)) :
      A i (some k) (g+t) = multiply (c i) (fun j => A i (some j) g)
        (fun j => A i (some j) t) k := (a i).map_forward_add_some φ g t k
  exact sector_cyclicProduct (G := fun i => ZMod (p i)) (K := fun i => Fin 2 × Fin (mₚ i))
    S A c h₀ h₁ x y

/-- Recovering the product on every sector suffices to recover the cyclic product. -/
theorem atTwo_grid_recover (x y : (∀ i, ZMod (p i)) → R)
    (z : (∀ i, PrimeAxisRow (mₚ i)) → R)
    (hz : ∀ S : Finset σ, z ∘ sector S =
      multiply (coeff (fun i : S => primeAxisActiveCoeff (m := mₚ i.val)
          (φ (ρₚ i.val)) (φ ((a i.val).beta))))
        ((columns (fun i => (a i).forward.map φ) *ᵥ x) ∘ sector S)
        ((columns (fun i => (a i).forward.map φ) *ᵥ y) ∘ sector S)) :
    columns (fun i => (a i).backward.map φ) *ᵥ z = cyclicProduct x y := by
  have he : z = columns (fun i => (a i).forward.map φ) *ᵥ cyclicProduct x y := by
    funext j
    obtain ⟨⟨s,k⟩,rfl⟩ := sectorEquiv.surjective j
    exact congrFun ((hz s).trans (atTwo_grid_sector a φ s x y).symm) k
  rw [he, mulVec_mulVec, columns_mul]
  simp only [AtTwoPrimeAxis.map_backward_mul_forward, columns_identity, one_mulVec]

end ConvolutionGrid

end FiniteFourier
end LinearAlgebra
end OAI
