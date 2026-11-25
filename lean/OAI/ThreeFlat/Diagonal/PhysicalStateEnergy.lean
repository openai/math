import OAI.ThreeFlat.Diagonal.PhysicalStage

namespace OAI
/-! # Changing coordinates in the energy and position count of a physical state -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression
open scoped BigOperators
noncomputable section

variable {d l : ℕ} {I : Type*} [Fintype I]

theorem State.positions_reindex (A : State d l) (f : I ≃ A.Base × BitWord l) :
    Fintype.card I = A.positions := Fintype.card_congr (f.trans A.chart)

theorem State.energy_reindex (A : State d l) (e : I ≃ (A.Base × Fin d) × BitWord l) :
    (∑ z : I, (A.width (e z) : ℝ)^2 / (1 / ((A.positions : ℝ)*d))) = A.energy := by
  unfold State.energy
  exact Fintype.sum_equiv e _ _ fun _ => rfl

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
