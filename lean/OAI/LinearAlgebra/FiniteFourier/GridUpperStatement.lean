import OAI.LinearAlgebra.FiniteFourier.GridFactor
import OAI.LinearAlgebra.FiniteFourier.Circuit
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # The uniform geometric grid upper estimate -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

universe v

/-- The geometric-grid theorem. Its constant is chosen before the field, grid
shape and individual matrices. An empty family represents a size-one grid. -/
def UniformGridUpper : Prop :=
  ∀ α : ℝ, 1 / 2 < α → ∃ C : ℝ, 0 < C ∧
    ∀ (K : Type v) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι]
      (a : ι → ℕ) (T : ∀ i, Matrix (Fin (a i)) (Fin (a i)) K),
      (∀ i, 2 ≤ a i) → (∀ i, GridFactor (T i)) →
      let N := ∏ i, a i
      (complexity (gridTensor T) : ℝ) ≤ C * N * (1 + Real.logb 2 N) ^ α

end

end

end FiniteFourier
end LinearAlgebra
end OAI
