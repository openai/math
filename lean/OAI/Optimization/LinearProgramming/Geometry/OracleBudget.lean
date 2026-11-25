import OAI.Optimization.LinearProgramming.Geometry.OracleBudgetAlgebra
import OAI.Optimization.LinearProgramming.Geometry.PivotBudgets
import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixContract

/-! Polynomial runtime and additive rational-register budgets for the pivot prefix
and the subsequent geometric label computation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelRAM

open RAM

/-- Coefficient contributed by the row collector after substituting the cubic precision. -/
def prefixWidthCoefficient : ℕ := 200000000000000 * 101^5

/-- Coefficient contributed by the Gram and Frank–Wolfe stages. -/
def postWidthCoefficient : ℕ := (640+10^50*1300^15)*217^105

theorem pivotTime_bound (r n C : ℕ) :
    r*PivotPrefixRAM.stepCost n (100*(n+1)^3) C ≤ r*C+3443*(r+n+1)^5 := by
  let z := r+n+1
  have hz : 0<z := by dsimp [z]; omega
  have hr : r≤z := by dsimp [z]; omega
  have hn : n≤z := by dsimp [z]; omega
  have hn' : n+1≤z := by dsimp [z]; omega
  have hb : (100*(n+1)^3) ≤ 100*z^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn' 3)
  have linear : 32*(100*(n+1)^3)+210 ≤ 32*(100*z^3)+210 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 32 hb) 210
  calc
    _ = r*C + r*(n*(32*(100*(n+1)^3)+210)+33) := by
      unfold PivotPrefixRAM.stepCost
      rw [Nat.add_assoc C, Nat.mul_add r C]
    _ ≤ r*C + z*(z*(32*(100*z^3)+210)+33) :=
      Nat.add_le_add_left (Nat.mul_le_mul hr (Nat.add_le_add_right (Nat.mul_le_mul hn linear) 33)) (r*C)
    _ ≤ _ := Nat.add_le_add_left (BudgetAlgebra.cubic_prefix z hz) (r*C)

theorem pivotWidth_bound (r n L extra : ℕ) :
    r*PivotPrefixRAM.stepWidth n L (100*(n+1)^3) extra ≤
      r*extra+prefixWidthCoefficient*(r+n+L+1)^16 := by
  let z := r+n+L+1
  have hz : 0<z := by dsimp [z]; omega
  have hr : r≤z := by dsimp [z]; omega
  have hn : n+1≤z := by dsimp [z]; omega
  have ha : n+L+1≤z := by dsimp [z]; omega
  have hz₃ : z ≤ z^3 := by simpa using Nat.pow_le_pow_right hz (show 1≤3 by decide)
  have hb : (100*(n+1)^3) ≤ 100*z^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 3)
  have hχ : n+L+(100*(n+1)^3)+1 ≤ 101*z^3 := by omega
  have hinc := (PivotStageRAM.widthIncrement_le n L (100*(n+1)^3)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hχ 5))
  calc
    _ = r*extra + r*PivotStageRAM.widthIncrement n L (100*(n+1)^3) := Nat.mul_add ..
    _ ≤ r*extra + z*(200000000000000*(101*z^3)^5) := Nat.add_le_add_left (Nat.mul_le_mul hr hinc) _
    _ = _ := congrArg (fun a => r*extra+a) (BudgetAlgebra.fifth_cube_product z 200000000000000 101)

/-- The caller may price its determinant and reply subroutine independently. -/
theorem time_budget {r n N C c e post : ℕ} (hsize : r+n≤N) (hC : C≤polyBound c e N)
    (hpost : post≤polyBound 510000000 9 (r+n)) :
    r*PivotPrefixRAM.stepCost n (100*(n+1)^3) C+post+12 ≤
      polyBound (c+510004000) (max (e+1) 9) N :=
  BudgetAlgebra.combined_time hsize hC (pivotTime_bound r n C) hpost

/-- Each label call adds a fixed polynomial to an arbitrary incoming width.
The width of unrelated registers never enters a higher power. -/
theorem width_budget {r n N L extra H l d x f post postExponent : ℕ} (hsize : r+n ≤ N)
    (hL : L≤polyBound l d N) (hX : extra≤polyBound x f N)
    (hpost : post≤polyBound postWidthCoefficient postExponent (r+n)) :
    max (H+r*PivotPrefixRAM.stepWidth n L (100*(n+1)^3) extra) post ≤
      H+polyBound (x+prefixWidthCoefficient*(l+1)^16+postWidthCoefficient)
        (max (f+1) (max (max d 1 * 16) postExponent)) N :=
  BudgetAlgebra.combined_width hsize hL hX (pivotWidth_bound r n L extra) hpost

/-- Substitute polynomial source and reply widths into an additive per-call bound. -/
theorem substitute_local_width {r n E G H N c q coef degree w : ℕ}
    (hw : w≤H+polyBound coef degree (r+n+E+G)) (hsize : r+n≤N) (hloc : E+G≤polyBound c q N) :
    w≤H+polyBound (coef*(c+1)^degree) (max q 1 * degree) N :=
  BudgetAlgebra.compose_width hw hsize hloc

end LabelRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
