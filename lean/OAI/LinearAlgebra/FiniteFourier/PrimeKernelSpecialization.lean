import OAI.LinearAlgebra.FiniteFourier.IntegralGridInputs
import OAI.LinearAlgebra.FiniteFourier.PrimeBatchDescent

/-! # Specializing a fixed-prime Fourier circuit along a coefficient homomorphism -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

section Coefficients

variable {R S I O : Type*} [Semiring R] [Semiring S]

/-- Applying a coefficient homomorphism to every gate and readout preserves the gate budget. -/
theorem RealizableAtMost.mapCoeff {M : Matrix O I R} {s : ℕ}
    (h : RealizableAtMost M s) (φ : R →+* S) : RealizableAtMost (M.map φ) s := by
  obtain ⟨r, hr, p, rfl⟩ := h
  exact ⟨r, hr, p.mapCoeff φ, p.matrix_mapCoeff φ⟩

/-- The specialized matrix can be realized with the size of an optimal source circuit. -/
theorem complexity_mapCoeff_le [Fintype I] [Fintype O] (φ : R →+* S) (M : Matrix O I R) :
    complexity (M.map φ) ≤ complexity M :=
  (complexity_le_iff ..).2 ((realizableAtMost_complexity M).mapCoeff φ)

end Coefficients

/-- A Fourier kernel bound specializes to any image of its generating root. -/
theorem complexity_primeTransform_map_le {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (ℓ k : ℕ) (ζ : R) :
    complexity (primeTransform ℓ k (φ ζ)) ≤ complexity (primeTransform ℓ k ζ) := by
  rw [← primeTransform_map]
  exact complexity_mapCoeff_le φ _

end FiniteFourier
end LinearAlgebra
end OAI
