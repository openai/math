import OAI.ThreeFlat.Diagonal.PhysicalMoveShrinkWidth
import OAI.ThreeFlat.Diagonal.PhysicalMoveRefreshWidth
import OAI.ThreeFlat.Diagonal.PhysicalStageProgram

namespace OAI
/-! # A product of width allowances for the chronological physical program -/

namespace ThreeFlat.Diagonal.PhysicalStage.Program

noncomputable section
variable {F : Type} [Field F]

def widthCost : {s : ℕ} → Program F s → ℕ
  | _, .done _ => 1
  | _, .shrink s _ T _ tail => (1+shrinkWidthFactor T s) * tail.widthCost
  | _, .refresh _ _ _ _ _ _ _ T _ _ _ _ _ _ _ tail => (1+refreshWidthFactor T) * tail.widthCost

theorem widthCost_pos {s : ℕ} (P : Program F s) : 0 < P.widthCost := by
  induction P with
  | done => exact Nat.one_pos
  | shrink _ _ _ _ _ ih => exact Nat.mul_pos (by omega) ih
  | refresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact Nat.mul_pos (by omega) ih

end
end ThreeFlat.Diagonal.PhysicalStage.Program

end OAI
