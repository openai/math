import OAI.LinearAlgebra.FiniteFourier.SlotProducts
import OAI.LinearAlgebra.FiniteFourier.PhaseValueLaws

/-! # The value of the empty matrix tensor power -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical
variable {K : Type*} [Field K] {R C : Type} [Fintype R] [Fintype C]

/-- Every local format in the empty product has one basis element. Its
coefficient is the empty product `1`, giving the tensor semiring unit. -/
theorem phasePointValue_slotPower_zero
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 4) K → _ → Prop))
    (a : R × C → K) : phasePointValue φ (slotMatrix (slotPower a 0)) = 1 := by
  let T := phaseRaw (slotMatrix (slotPower a 0))
  have equiv_nonempty (i : Fin 4) : Nonempty (T.Leg i ≃ PUnit) := by
    change Nonempty (phaseLeg (Fin 0 → R) (Fin 0 → C) i ≃ PUnit)
    fin_cases i <;> first | exact ⟨Equiv.ofUnique (Fin 0 → R) _⟩ | exact ⟨Equiv.ofUnique (Fin 0 → C) _⟩
  let eqv i := (equiv_nonempty i).some
  have hT : ofRaw T = (1 : TensorClass.{0} (Fin 4) K) := by
    rw [← ofRaw_one]
    apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent eqv ?_)
    intro z
    change (phaseRaw (slotMatrix (slotPower a 0))).coeff z = 1
    change phaseEntry (slotMatrix (slotPower a 0)) (z 2) (z 3) (z 0) (z 1) = 1
    have hr : z 2 = z 0 := Subsingleton.elim (α := Fin 0 → R) _ _
    have hc : z 3 = z 1 := Subsingleton.elim (α := Fin 0 → C) _ _
    simp [phaseEntry, slotMatrix, slotPower, hr, hc]
    exact ⟨rfl, rfl⟩
  change (φ.val (ofRaw T) : ℝ) = 1
  rw [hT, φ.property.2.1, NNReal.coe_one]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
