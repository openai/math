import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionCyclotomicNodes
import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionQuadraticIso
import OAI.LinearAlgebra.FiniteFourier.QuadraticPeriods

/-! # Quadratic deformation on the prime axes at two

For a prime of residue three modulo four the quadratic period parameter is the integer
`(p + 1) / 4` and the discriminant is `-p`. This makes the endpoint constructions
available in every finite jet over the two-local coefficient ring.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial

variable {p : ℕ}

/-- The prime-axis length and its half-length are both odd at residue three modulo four. -/
theorem primeAxis_odd_parameters (hp : p % 4 = 3) : Odd p ∧ Odd ((p-1)/2) := by
  constructor
  · exact ⟨p/2, by omega⟩
  · exact ⟨p/4, by omega⟩

/-- The division by four is performed on integers before passing to the coefficient ring. -/
theorem primeAxis_discriminant (R : Type*) [CommRing R] (hp : p % 4 = 3) :
    1 - 4 * (((p+1)/4 : ℕ) : R) = -(p : R) := by
  have h : 4 * ((p+1)/4) = p+1 := by omega
  have h' : (4 : R) * (((p+1)/4 : ℕ) : R) = (p : R)+1 := by
    simpa using congrArg (Nat.cast : ℕ → R) h
  rw [h']
  abel

/-- The prime, the binomial derivative and the quadratic discriminant are units
in the jet coefficient ring. -/
theorem primeAxis_jet_units (M h : ℕ) (hp : p % 4 = 3) :
    IsUnit (p : IntegralJet M h) ∧ IsUnit (((p-1)/2 : ℕ) : IntegralJet M h) ∧
      IsUnit (1 - 4 * (((p+1)/4 : ℕ) : IntegralJet M h)) := by
  obtain ⟨hp', hm⟩ := primeAxis_odd_parameters hp
  have pu := isUnit_odd_inIntegralJet M h hp'
  exact ⟨pu, isUnit_odd_inIntegralJet M h hm, by rw [primeAxis_discriminant (IntegralJet M h) hp]; exact pu.neg⟩

/-- The coordinate `z` of the jet over the two-local cyclotomic coefficients. -/
noncomputable abbrev integralJetParameter (M h : ℕ) : IntegralJet M h :=
  AdjoinRoot.root ((X : (CyclotomicCoefficients TwoLocalQuadratic M)[X]) ^ h)

/-- At zero, the quadratic prime-axis factor of the long jet splits at the two
lifted roots in their prescribed residue order. -/
theorem primeQuadraticAxisAtZero (p M H : ℕ) :
    let z := integralJetParameter M H
    let ρ : IntegralJet M H := ((p+1)/4 : ℕ)
    ∃ e : QuadraticAxis (ρ*z) ≃ₐ[IntegralJet M H] IntegralJet M H × IntegralJet M H,
      z ∣ (e (AdjoinRoot.root _)).1 ∧ z ∣ (e (AdjoinRoot.root _)).2 + 1 :=
  exists_quadraticAxisSplitAtZero _ _ (jetParameter_nilpotent _ H)

/-- The short-jet endpoint gives the original quadratic factor, with identity
change of generator modulo the jet parameter. -/
theorem primeQuadraticAxisAtOne (M r : ℕ) (hp : p % 4 = 3) :
    let z := integralJetParameter M r
    let ρ : IntegralJet M r := ((p+1)/4 : ℕ)
    ∃ e : QuadraticAxis (ρ*(1+z)) ≃ₐ[IntegralJet M r] QuadraticAxis ρ,
      algebraMap (IntegralJet M r) _ z ∣ e (AdjoinRoot.root _) - AdjoinRoot.root _ :=
  exists_quadraticAxisChangeAtOne _ _ (jetParameter_nilpotent _ r) (primeAxis_jet_units M r hp).2.2

/-- In the prime cyclotomic quotient, the original generator is the sum on the
square orbit. Its simple root lifts uniquely after deformation over the short jet. -/
theorem primeSquarePeriodAtOne (M r : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    let J := IntegralJet M r
    let A := AdjoinRoot (cyclotomic p J)
    let z : A := algebraMap J A (integralJetParameter M r)
    let ρ : A := ((p+1)/4 : ℕ)
    let U := quadraticPeriod (primeAxisCharacter J p) 1
    ∃! v : A, z ∣ v - U ∧ v^2 + v + ρ*(1+z) = 0 := by
  let J := IntegralJet M r
  let A := AdjoinRoot (cyclotomic p J)
  have hp' : IsUnit (p : A) := by
    simpa only [map_natCast] using (primeAxis_jet_units M r hp).1.map (algebraMap J A)
  have hd : IsUnit (1 - 4 * (((p+1)/4 : ℕ) : A)) := by
    rw [primeAxis_discriminant A hp]
    exact hp'.neg
  have hU := primeAxis_square_period J p hp
  exact quadraticRootAtOne ((jetParameter_nilpotent _ r).map (algebraMap J A)) hU
    (quadraticDerivative_isUnit hU hd)

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
