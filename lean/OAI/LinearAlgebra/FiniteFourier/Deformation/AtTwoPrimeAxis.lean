import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeMatrix
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeCoefficients

/-! # The prime-axis transform over the cyclotomic coefficient order at two

Select the separated roots and the two-orbit presentation over the coefficient
order. Applying a coefficient homomorphism then gives the very same transform
in either jet, including its inverse and the undeformed multiplication law.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial Module TensorProduct Matrix

local notation:max "O₂ " M:arg => CyclotomicCoefficients TwoLocalQuadratic M

/-- Chosen Fourier nodes and the accompanying binomial factor on a selected prime axis. -/
structure AtTwoPrimeAxis (M p : ℕ) [Fact p.Prime] (hM : Odd M) (hp : p % 4 = 3) (hp7 : 7 ≤ p) where
  root : (O₂ M)ˣ
  root_eq : (root : O₂ M) = AdjoinRoot.root (cyclotomic M TwoLocalQuadratic)^(M/((p-1)/2))
  root_pow : root^((p-1)/2) = 1
  separated : ∀ i j : Fin ((p-1)/2), i ≠ j → IsUnit ((root : O₂ M)^i.val - (root : O₂ M)^j.val)
  factor : letI := atTwoCoefficients_nontrivial hM.pos
           AtTwoPrimeFactor (O₂ M) (PrimeAxisCosets.ofPrime p hp) root hp7

/-- All the data for the prime axis come from the single odd cyclotomic coefficient order. -/
noncomputable def atTwoPrimeAxis {M p : ℕ} [Fact p.Prime] (hM : Odd M)
    (hp : p % 4 = 3) (hp7 : 7 ≤ p) (hd : (p-1)/2 ∣ M) : AtTwoPrimeAxis M p hM hp hp7 := by
  letI := atTwoCoefficients_nontrivial hM.pos
  apply Classical.choice
  obtain ⟨u, heq, hu, hs, ⟨f⟩⟩ := atTwoCoefficients_primeFactor hM hp hp7 hd
  exact ⟨⟨u, heq, hu, hs, f⟩⟩

namespace AtTwoPrimeAxis

variable {M p : ℕ} [Fact p.Prime] {hM : Odd M} {hp : p % 4 = 3} {hp7 : 7 ≤ p}
  (a : AtTwoPrimeAxis M p hM hp hp7)

local notation "mₚ" => (p-1)/2
local notation "ρₚ" => (((p+1)/4 : ℕ) : O₂ M)

/-- Unit controlling the binomial relation on the active factor. -/
noncomputable abbrev beta : (O₂ M)ˣ := by
  letI := atTwoCoefficients_nontrivial hM.pos
  exact a.factor.beta

/-- Full cyclic algebra split into its scalar and nonscalar factors. -/
noncomputable def equiv : BinomialAxis p (1 : O₂ M) ≃ₐ[O₂ M]
    (O₂ M) × (QuadraticAxis ρₚ ⊗[O₂ M] BinomialAxis mₚ (a.beta : O₂ M)) := by
  letI := atTwoCoefficients_nontrivial hM.pos
  exact primeAxisProductEquiv (primeCyclicCRT _ _ (atTwoCoefficients_isUnit_odd M
    (primeAxis_odd_parameters hp).1)) a.factor.equiv

/-- The prime-axis transform before scalar extension to a jet. -/
noncomputable def forward : Matrix (PrimeAxisRow mₚ) (ZMod p) (O₂ M) := by
  letI := atTwoCoefficients_nontrivial hM.pos
  exact primeAxisMatrix (by omega) a.equiv

/-- The inverse prime-axis transform over the coefficient order. -/
noncomputable def backward : Matrix (ZMod p) (PrimeAxisRow mₚ) (O₂ M) := by
  letI := atTwoCoefficients_nontrivial hM.pos
  exact primeAxisInvMatrix (by omega) a.equiv

@[simp] theorem backward_mul_forward : a.backward * a.forward = 1 := by
  let := atTwoCoefficients_nontrivial hM.pos
  exact primeAxisInvMatrix_mul _ _

@[simp] theorem forward_mul_backward : a.forward * a.backward = 1 := by
  let := atTwoCoefficients_nontrivial hM.pos
  exact primeAxisMatrix_mul_inv _ _

@[simp] theorem forward_none (g : ZMod p) : a.forward none g = 1 := by
  let := atTwoCoefficients_nontrivial hM.pos
  change primeAxisMatrix _ _ none g = 1
  rw [primeAxisMatrix_none, equiv, primeAxisProductEquiv, AlgEquiv.trans_apply, primeCyclicCRT_basis]
  rfl

theorem forward_add_some (g t : ZMod p) (k : Fin 2 × Fin mₚ) :
    a.forward (some k) (g+t) = multiply (primeAxisActiveCoeff ρₚ (a.beta : O₂ M))
      (fun j => a.forward (some j) g) (fun j => a.forward (some j) t) k := by
  let := atTwoCoefficients_nontrivial hM.pos
  exact primeAxisMatrix_add_some _ _ g t k

section Map

variable {S : Type*} [CommRing S] (φ : O₂ M →+* S)

@[simp] theorem map_backward_mul_forward : a.backward.map φ * a.forward.map φ = 1 := by
  rw [← Matrix.map_mul, backward_mul_forward, Matrix.map_one] <;> simp

@[simp] theorem map_forward_mul_backward : a.forward.map φ * a.backward.map φ = 1 := by
  rw [← Matrix.map_mul, forward_mul_backward, Matrix.map_one] <;> simp

@[simp] theorem map_forward_none (g : ZMod p) : a.forward.map φ none g = 1 := by
  simp [Matrix.map_apply]

private theorem map_activeCoeff {m : ℕ} (ρ β : O₂ M) (i j k : Fin 2 × Fin m) :
    φ (primeAxisActiveCoeff ρ β i j k) = primeAxisActiveCoeff (φ ρ) (φ β) i j k := by
  simp only [primeAxisActiveCoeff, quadraticCoeff, binomialCoeff, binomial, eval_mul]
  split_ifs <;> simp

/-- Scalar extension preserves the cyclic column law on the nonscalar rows, with
both deformation parameters transported along the same coefficient map. -/
theorem map_forward_add_some (g t : ZMod p) (k : Fin 2 × Fin mₚ) :
    a.forward.map φ (some k) (g+t) = multiply (primeAxisActiveCoeff (φ ρₚ) (φ (a.beta : O₂ M)))
      (fun j => a.forward.map φ (some j) g) (fun j => a.forward.map φ (some j) t) k := by
  simpa only [Matrix.map_apply, map_multiply, Function.comp_def, map_activeCoeff] using
    congrArg φ (a.forward_add_some g t k)

end Map

end AtTwoPrimeAxis

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
