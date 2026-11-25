import Mathlib.Data.List.FinRange
import Mathlib.Data.Rat.Defs

/-! The nonzero columns that remain in an increasing signed-minor scan. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

variable {n : ℕ}

/-- Candidate scan from column j, retaining exactly the nonzero determinants. -/
def tailColumns (raw : Fin n → ℚ) (j : ℕ) : List (Fin n) :=
  ((List.finRange n).drop j).filter fun a => raw a ≠ 0

@[simp] theorem tailColumns_end (raw : Fin n → ℚ) : tailColumns raw n=[]  := by
  rw [tailColumns,List.drop_of_length_le (by simp)]
  rfl

theorem tailColumns_step (raw : Fin n → ℚ) (j : Fin n) :
    tailColumns raw j.val = if raw j = 0 then tailColumns raw (j.val+1) else j::tailColumns raw (j.val+1) := by
  unfold tailColumns
  rw [List.drop_eq_getElem_cons (by simp)]
  by_cases hz : raw j=0 <;> simp [hz]

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
