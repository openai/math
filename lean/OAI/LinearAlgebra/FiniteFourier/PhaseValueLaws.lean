import OAI.LinearAlgebra.FiniteFourier.PhasePrice
import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
import OAI.LinearAlgebra.SpectralBooks.ScalarRestriction

/-! # Spectral values of sums and scalar multiples of controlled phases -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

variable {K : Type*} [Field K] {R C : Type} [Fintype R] [Fintype C]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 4) K → _ → Prop))

/-- The real-valued evaluation of a controlled phase by a normalized point. -/
def phasePointValue (M : Matrix R C K) : ℝ := φ.val (ofRaw (phaseRaw M))

theorem phasePointValue_nonneg (M : Matrix R C K) : 0 ≤ phasePointValue φ M :=
  NNReal.coe_nonneg _

@[simp] theorem phasePointValue_zero : phasePointValue φ (0 : Matrix R C K) = 0 := by
  have h : (phaseRaw (0 : Matrix R C K)).coeff = 0 := by
    by_contra hn
    exact (phaseRaw_coeff_ne_zero.mp hn) rfl
  simp [phasePointValue, (ofRaw_eq_zero_iff _).mpr h, φ.2.1]

private abbrev phaseCoeffs (M : Matrix R C K) : ((i : Fin 4) → phaseLeg R C i) → K :=
  (phaseRaw M).coeff

private theorem phaseRaw_coeff_add (M N : Matrix R C K) : phaseCoeffs (M + N) =
    phaseCoeffs M + phaseCoeffs N := by
  funext z
  change (phaseRaw (M + N)).coeff z = (phaseRaw M).coeff z + (phaseRaw N).coeff z
  rw [phaseRaw_coeff (M + N) z, phaseRaw_coeff M z, phaseRaw_coeff N z]
  simp only [phaseEntry]
  split <;> simp_all
  rfl

/-- Local block addition maps the direct sum of the two phases to the phase
of the matrix sum. -/
theorem phasePointValue_add_le (M N : Matrix R C K) :
    phasePointValue φ (M + N) ≤ phasePointValue φ M + phasePointValue φ N := by
  have hr : (phaseRaw (M + N)).Restricts ((phaseRaw M).add (phaseRaw N)) := by
    change Crossing.IsRestriction (phaseCoeffs (M + N)) (sumCoeff (phaseCoeffs M) (phaseCoeffs N))
    rw [phaseRaw_coeff_add]
    exact ordinary_add_restricts _ _
  have h := φ.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr hr)
  simpa [phasePointValue, φ.2.2.2.1] using (NNReal.coe_le_coe.mpr h)

private theorem phaseRaw_coeff_smul (a : K) (M : Matrix R C K) :
    phaseCoeffs (a • M) = a • phaseCoeffs M := by
  funext z
  change (phaseRaw (a • M)).coeff z = a * (phaseRaw M).coeff z
  rw [phaseRaw_coeff (a • M) z, phaseRaw_coeff M z]
  simp only [phaseEntry]
  split <;> simp_all
  rfl

/-- Scaling one local map realizes the phase of an arbitrary scalar multiple. -/
theorem phasePointValue_smul_le (a : K) (M : Matrix R C K) :
    phasePointValue φ (a • M) ≤ phasePointValue φ M := by
  have hr : (phaseRaw (a • M)).Restricts (phaseRaw M) := by
    change Crossing.IsRestriction (phaseCoeffs (a • M)) (phaseCoeffs M)
    rw [phaseRaw_coeff_smul]
    exact scalar_mul_restricts a _
  exact NNReal.coe_le_coe.mpr (φ.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr hr))

end

end

end FiniteFourier
end LinearAlgebra
end OAI
