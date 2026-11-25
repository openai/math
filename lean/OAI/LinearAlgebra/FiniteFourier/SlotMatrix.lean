import Mathlib.Data.Matrix.Basic

/-! # Grouping the row and column indices of powered matrices -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K I O : Type*} [Zero K]

/-- Group the row and column labels of several matrix slots. -/
def slotMatrix {j : ℕ} (a : (Fin j → O × I) → K) : Matrix (Fin j → O) (Fin j → I) K :=
  fun row col ↦ a (fun l ↦ (row l, col l))

/-- The slot-array and matrix presentations have identical entries in both directions. -/
theorem slotMatrix_eq_zero_iff {j : ℕ} {a : (Fin j → O × I) → K} : slotMatrix a = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext x
    exact congrFun (congrFun h (fun t ↦ (x t).1)) (fun t ↦ (x t).2)
  · rintro rfl
    rfl

end FiniteFourier
end LinearAlgebra
end OAI
