import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI
/-! # Numerical bounds for physical stages -/

namespace ThreeFlat.Diagonal.PhysicalStage
noncomputable section

/-- Bounds for the energy and number of physical sites. -/
structure Totals where
  energy : ℝ
  sites : ℝ

/-- The affine energy estimate and the change in site count of one pass. -/
structure Effect where
  leading : ℝ
  error : ℝ
  shrink : Bool

def Effect.apply (v : Totals) (u : Effect) : Totals :=
  ⟨u.leading*v.energy + u.error*v.sites^2, if u.shrink then v.sites/4 else v.sites⟩

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
