import OAI.ThreeFlat.Diagonal.PhysicalBlockSchedule
import OAI.ThreeFlat.Diagonal.PhysicalProgramWidthCost

namespace OAI
/-! # The width cost of a repeated physical block -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block

noncomputable section
variable {F : Type} [Field F] (B : Block F)

/-- One complete block is measured with an empty continuation. -/
def widthBase : ℕ := (B.prefix (.done _)).widthCost

theorem widthBase_pos : 0 < B.widthBase := (B.prefix (.done _)).widthCost_pos

private theorem widthCost_cast {s t : ℕ} (e : s=t) (p : Program F s) :
    (e ▸ p : Program F t).widthCost = p.widthCost := by
  subst t
  rfl

private def shrinkCost : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n+1, i => (1+shrinkWidthFactor B.shrink (B.exponent i))*shrinkCost n (i+1)

private theorem widthCost_shrinkPrefix (n i : ℕ) (tail : Program F (B.exponent (i+n))) :
    (B.shrinkPrefix n i tail).widthCost = B.shrinkCost n i * tail.widthCost := by
  induction n generalizing i with
  | zero => simp only [shrinkPrefix,shrinkCost,Nat.one_mul]
  | succ n ih =>
    simp only [shrinkPrefix,Program.widthCost,ih,widthCost_cast,shrinkCost,Nat.mul_assoc]

theorem widthCost_prefix (tail : Program F (B.exponent 0)) :
    (B.prefix tail).widthCost = B.widthBase*tail.widthCost := by
  simp only [widthBase,«prefix»,widthCost_shrinkPrefix,widthCost_cast,Program.widthCost,
    Nat.mul_one,Nat.mul_assoc]

theorem widthCost_repeat_eq_pow (n : ℕ) : (B.repeat n).widthCost = B.widthBase^n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Block.repeat, widthCost_prefix, ih, pow_succ']

theorem widthCost_repeat_le (n : ℕ) :
    (B.repeat n).widthCost ≤ B.widthBase^((B.levels+1)*n) := by
  rw [widthCost_repeat_eq_pow]
  exact Nat.pow_le_pow_right B.widthBase_pos (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))

end
end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
