import OAI.LinearAlgebra.SpectralBooks.Prices
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Split

/-! # A finite marked basis for tensor powers

Writing the powered marked leg as a single finite type supplies precisely
the basis labels used by the exterior operators.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace SiteTensor.Relocation

variable {I J Q : Type} {A : I → Type} [Fintype I] [Fintype J] [Fintype Q]
variable [∀ i, Fintype (A i)] {K : Type*} [Field K]

/-- Coefficients of a tensor power in background and marked coordinates. -/
def powerCoeff (n : ℕ) (T : (∀ i, A i) → Q → K) (x : ∀ i, Fin n → A i) (q : Fin n → Q) : K :=
  ∏ k, T (fun i => x i k) (q k)

/-- Enumerate the powered marked basis. -/
def powerMarkEquiv (Q : Type) [Fintype Q] (n : ℕ) : Fin ((Fintype.card Q)^n) ≃ (Fin n → Q) :=
  (Fintype.equivFinOfCardEq (by simp)).symm

/-- Coefficients of the marked power with its marked basis enumerated. -/
def finPowerCoeff (n : ℕ) (T : (∀ i, A i) → Q → K) (x : ∀ i, Fin n → A i)
    (q : Fin ((Fintype.card Q)^n)) : K :=
  powerCoeff n T x (powerMarkEquiv Q n q)

variable (n : ℕ) (T : (∀ i, A i) → Q → K)

/-- The marked power with any equivalent marking basis has the tensor power's class. -/
theorem marked_power_equivalent {D : Type} [Fintype D] (e : D ≃ (Fin n → Q)) :
    (marked (fun i => Fin n → A i) D (fun x q => powerCoeff n T x (e q))).Equivalent
      ((marked A Q T).powerTensor n) := by
  let f (i : I ⊕ Unit) :
      (marked (fun i => Fin n → A i) D (fun x q => powerCoeff n T x (e q))).Leg i ≃
        ((marked A Q T).powerTensor n).Leg i := by
    rcases i with i | ⟨⟩
    · exact Equiv.refl _
    · exact e
  apply Raw.reindex_equivalent f
  intro x
  rfl

variable [Nonempty J] (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)

private theorem price_power_basis {D : Type} [Fintype D] (e : D ≃ (Fin n → Q)) (σ : I ⊕ Unit → J) :
    rawLogPrice φ c ((marked (fun i => Fin n → A i) D (fun x q => powerCoeff n T x (e q))).group σ) =
      n * rawLogPrice φ c ((marked A Q T).group σ) := by
  have h := congrArg (groupClass (K := K) σ) (ofRaw_eq_iff.mpr (marked_power_equivalent n T e))
  change ofRaw _ = ofRaw _ at h
  rw [← rawLogPrice_group_powerTensor φ c (marked A Q T) σ n]
  exact congrArg (fun S => c * Real.logb 2 (φ.val S : ℝ)) h

/-- The price of the powered coefficient array at any placement. -/
theorem rawLogPrice_marked_power (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    (c : ℝ) (n : ℕ) (T : (∀ i, A i) → Q → K) (σ : I ⊕ Unit → J) :
    rawLogPrice φ c ((marked (fun i => Fin n → A i) (Fin n → Q) (powerCoeff n T)).group σ) =
      n * rawLogPrice φ c ((marked A Q T).group σ) :=
  price_power_basis n T φ c (Equiv.refl _) σ

/-- Enumerating the powered marked basis preserves the price at every placement. -/
theorem rawLogPrice_marked_finPower (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    (c : ℝ) (n : ℕ) (T : (∀ i, A i) → Q → K) (σ : I ⊕ Unit → J) :
    rawLogPrice φ c ((marked (fun i => Fin n → A i) (Fin ((Fintype.card Q)^n))
      (finPowerCoeff n T)).group σ) = n * rawLogPrice φ c ((marked A Q T).group σ) :=
  price_power_basis n T φ c (powerMarkEquiv Q n) σ

/-- The enumerated marked power of a nonzero tensor is nonzero. -/
theorem marked_finPower_ne_zero (hT : (marked A Q T).coeff ≠ 0) :
    (marked (fun i => Fin n → A i) (Fin ((Fintype.card Q)^n)) (finPowerCoeff n T)).coeff ≠ 0 := by
  have h := ofRaw_eq_iff.mpr (marked_power_equivalent n T (powerMarkEquiv Q n))
  intro hz
  have he := (ofRaw_eq_zero_iff _).mpr hz
  exact (Raw.powerTensor_ne_zero _ hT n) ((ofRaw_eq_zero_iff _).mp (h.symm.trans he))

end SiteTensor.Relocation

end

end SpectralBooks
end LinearAlgebra
end OAI
