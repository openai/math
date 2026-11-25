import OAI.LinearAlgebra.FiniteFourier.AtTwoPrimeBlockBasis
import OAI.LinearAlgebra.FiniteFourier.AtTwoPrimePeriods
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimePresentation
import OAI.LinearAlgebra.FiniteFourier.PrimeAxisEigenspace
import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionPrimeQuadratic

/-! # The nonscalar prime-axis factor over the odd-denominator coefficients

In the two-orbit Fourier basis, the fixed algebra has basis `1,U`.
Multiplication by a unit of frequency one shifts that basis to each
frequency. The resulting monomials identify the nonscalar factor with
the tensor of its quadratic and binomial presentations.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial Module TensorProduct

variable (R : Type*) [CommRing R] [Nontrivial R] {p : ℕ} [Fact p.Prime]
  (C : PrimeAxisCosets p) (u : Rˣ)

local notation "mₚ" => (p - 1) / 2
local notation "Aₚ" => AdjoinRoot (cyclotomic p R)
local notation "ρₚ" => (((p + 1) / 4 : ℕ) : R)
local notation "Uₚ" => quadraticPeriod (primeAxisCharacter R p) 1
local notation "σₚ" => primeAxisAction R p C.generator

/-- The unit binomial constant, its frequency-one root, and the prime-axis
presentation in the specified power coordinates. -/
structure AtTwoPrimeFactor (hp7 : 7 ≤ p) where
  beta : Rˣ
  generator : Aₚˣ
  generator_eq : (generator : Aₚ) = atTwoPrimeFourier R C u false ⟨1, by omega⟩ +
    atTwoPrimeFourier R C u true ⟨1, by omega⟩
  equiv : (QuadraticAxis ρₚ ⊗[R] BinomialAxis mₚ (beta : R)) ≃ₐ[R] Aₚ
  equiv_basis (i : Fin 2 × Fin mₚ) :
    equiv (((quadraticBasis ρₚ).tensorProduct (binomialBasis (by omega : 0 < mₚ) (beta : R))) i) =
      Uₚ ^ i.1.val * (generator : Aₚ) ^ i.2.val
  eigen_basis (i : Fin 2 × Fin mₚ) :
    σₚ (Uₚ ^ i.1.val * (generator : Aₚ) ^ i.2.val) =
      (u:R)^i.2.val • (Uₚ ^ i.1.val * (generator : Aₚ) ^ i.2.val)

/-- The two-orbit presentation for any base with an invertible prime and
a separated system of roots of unity of the half-length. -/
noncomputable def atTwoPrimeFactor (hp : p % 4 = 3) (hp7 : 7 ≤ p)
    (hpR : IsUnit (p : R)) (hm : IsUnit ((mₚ : ℕ) : R)) (hu : u^mₚ = 1)
    (hs : ∀ i j : Fin mₚ, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val)) :
    AtTwoPrimeFactor R C u hp7 := by
  classical
  apply Classical.choice
  obtain ⟨β, Y, e₀, h₀, h₁, hY, heY, _, hpow⟩ :=
    exists_atTwoPrimePeriod_data R C u hp hp7 hpR hm hu hs
  let σ := σₚ
  have hmpos : 0 < mₚ := by omega
  obtain ⟨b, hb⟩ := exists_atTwoPrimeFourier_basis R C u hmpos hm hu hs
  have hbσ (c : Bool) (j : Fin mₚ) : σ.toLinearMap (b (c,j)) = (u:R)^j.val • b (c,j) := by
    rw [hb]; exact atTwoPrimeFourier_eigen R C u hu c j
  choose v hv₀ hv₁ using fun j : Fin mₚ =>
    exists_primeAxisEigenspace_basis σ u Y heY Uₚ e₀ h₀ h₁ j.val
  obtain ⟨e, he⟩ := exists_cyclicEigen_basis σ.toLinearMap u hu hm hs b hbσ v
  have e₀' (j : Fin mₚ) := (he 0 j).trans (hv₀ j)
  have e₁' (j : Fin mₚ) := (he 1 j).trans (hv₁ j)
  have hU : Uₚ ^ 2 + Uₚ + algebraMap R Aₚ ρₚ = 0 := by
    simpa only [map_natCast] using primeAxis_square_period R p hp
  let f := primeAxisPresentationEquiv hmpos hU hpow e e₀' e₁'
  have hmon (i : Fin 2 × Fin mₚ) : e i = Uₚ^i.1.val * (Y:Aₚ)^i.2.val := by
    rcases i with ⟨i,j⟩
    fin_cases i <;> simp [e₀', e₁']
  refine ⟨⟨β, Y, hY, f, fun i => (primeAxisPresentationEquiv_basis ..).trans (hmon i), ?_⟩⟩
  rintro ⟨i,j⟩
  rw [← hmon (i,j), he]
  exact Module.End.mem_eigenspace_iff.mp (v j i).property

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
