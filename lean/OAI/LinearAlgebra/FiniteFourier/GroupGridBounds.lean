import OAI.LinearAlgebra.FiniteFourier.Bounds
import OAI.LinearAlgebra.FiniteFourier.GridUpperStatement
import OAI.LinearAlgebra.FiniteFourier.GroupGrid

/-! # Specialization of the geometric grid upper estimate to character transforms -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

universe u v

/-- The geometric-grid algorithm gives the uniform upper half of the Fourier
complexity theorem with the same exponent and constants, in all characteristics. -/
theorem uniformFourierUpper_of_grid (hg : UniformGridUpper.{v}) : UniformFourierUpper.{u,v} := by
  classical
  intro ε hε
  obtain ⟨C, hc, h⟩ := hg (1/2 + ε) (by linarith)
  refine ⟨C, hc, ?_⟩
  intro G K _ _ _ had _
  obtain ⟨D⟩ := exists_fourierGrid G K had
  have hgrid := h K D.Axis D.size (fun i => geometricMatrix (D.size i) (D.root i))
    D.two_le D.gridFactor
  dsimp only at hgrid
  rw [D.prod_size] at hgrid
  rw [(D.complexity_eq had).1]
  exact hgrid

end FiniteFourier
end LinearAlgebra
end OAI
