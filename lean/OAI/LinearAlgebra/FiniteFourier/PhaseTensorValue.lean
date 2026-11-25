import OAI.LinearAlgebra.FiniteFourier.PhaseUnitValue

/-! # Tensor values obtained from the spectrum of controlled phases -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

variable {K : Type*} [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 4) K → _ → Prop))
variable {R C S D : Type} [Fintype R] [Fintype C] [Fintype S] [Fintype D]

theorem phasePointValue_submatrix (M : Matrix R C K) (r : S ≃ R) (c : D ≃ C) :
    phasePointValue φ (M.submatrix r c) = phasePointValue φ M := by
  simp only [phasePointValue, ofRaw_phaseRaw_submatrix]

theorem phasePointValue_kronecker (M : Matrix R C K) (N : Matrix S D K) :
    phasePointValue φ (M.kronecker N) = phasePointValue φ M * phasePointValue φ N := by
  simp only [Matrix.kronecker, phasePointValue, ofRaw_phaseRaw_kronecker, φ.2.2.2.2.1, NNReal.coe_mul]

theorem phasePointValue_slotPower_one (a : R × C → K) :
    phasePointValue φ (slotMatrix (slotPower a 1)) = phasePointValue φ (Matrix.of fun r c ↦ a (r, c)) := by
  rw [slotMatrix_power_one, phasePointValue_submatrix]

private theorem phasePointValue_interleave {k : ℕ} (s : Finset (Fin k))
    (a : (Fin s.card → R × C) → K) (b : (Fin sᶜ.card → R × C) → K) :
    phasePointValue φ (slotMatrix (fun x ↦ a (selectSlots s x) * b (selectSlots sᶜ x))) =
      phasePointValue φ (slotMatrix a) * phasePointValue φ (slotMatrix b) := by
  rw [slotMatrix_interleaved, phasePointValue_submatrix, phasePointValue_kronecker]

private theorem phasePointValue_power (a : R × C → K) (k : ℕ) :
    phasePointValue φ (slotMatrix (slotPower a k)) = phasePointValue φ (slotMatrix (slotPower a 1)) ^ k := by
  induction k with
  | zero => rw [phasePointValue_slotPower_zero, pow_zero]
  | succ k ih =>
    rw [slotMatrix_power_succ, phasePointValue_submatrix, phasePointValue_kronecker, ih,
      phasePointValue_slotPower_one, pow_succ']

/-- Evaluating all powered matrix formats by the same normalized phase point
gives the value used in the weighted coefficient estimates. -/
def tensorValueOfPhasePoint (O I : Type) [Fintype O] [Fintype I] :
    TensorValue K (O × I) where
  price _ a := phasePointValue φ (slotMatrix a)
  nonneg _ := phasePointValue_nonneg φ _
  zero _ := phasePointValue_zero φ
  add a b := phasePointValue_add_le φ (slotMatrix a) (slotMatrix b)
  scale c a := phasePointValue_smul_le φ c (slotMatrix a)
  interleave := phasePointValue_interleave φ
  power := phasePointValue_power φ

end

end

end FiniteFourier
end LinearAlgebra
end OAI
