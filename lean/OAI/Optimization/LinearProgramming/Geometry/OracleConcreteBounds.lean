import OAI.Optimization.LinearProgramming.Geometry.OracleBudget
import OAI.Optimization.LinearProgramming.Geometry.BorderLocalBudget
import OAI.Optimization.LinearProgramming.Geometry.OracleAssembly
import OAI.Optimization.LinearProgramming.Geometry.BorderBatchCode

/-! Closed bounds for the fixed geometric label segment, including its concrete
candidate-batch implementation and repeated calls in the same caller memory. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelRAM

open RAM

theorem time_polynomial {r n N C c e : ℕ} (hsize : r+n≤N) (hC : C≤polyBound c e N) :
    time r n C ≤ polyBound (c+510004000) (max (e+1) 9) N :=
  time_budget hsize hC (afterPrefixTime_polynomial r n)

theorem width_polynomial {r n N L extra H l d x f : ℕ} (hsize : r+n≤N)
    (hL : L≤polyBound l d N) (hX : extra≤polyBound x f N) :
    width r n L extra H ≤ H+polyBound (x+prefixWidthCoefficient*(l+1)^16+postWidthCoefficient)
      (max (f+1) (max (max d 1*16) 315)) N :=
  width_budget (postExponent:=315) hsize hL hX (afterPrefixBits_dimension r n)

theorem concreteTime_bound (r n : ℕ) :
    time r n (BorderBatch.batchTime r n) ≤ polyBound 510006600 9 (r+n) :=
  time_polynomial (c:=2600) (e:=8) le_rfl (BorderBatch.batchTime_formula_bound r n)

/-- Register-growth coefficient of the linked determinant scan, clipping replies,
Gram projector, and conditional-gradient test. -/
def concreteWidthCoefficient : ℕ := 40+prefixWidthCoefficient*11^16+postWidthCoefficient

theorem concreteWidth_bound (r n E G H : ℕ) :
    width r n (BorderBatch.batchLocalWidth n E G) (BorderBatch.batchIncrement n E G) H ≤
      H+polyBound concreteWidthCoefficient 315 (r+n+E+G) :=
  width_polynomial (N:=r+n+E+G) (l:=10) (d:=4) (x:=40) (f:=4) (by omega)
    (BorderBatch.batchLocalWidth_bound r n E G)
    (BorderBatch.batchIncrement_bound r n E G)

/-- The raw determinant-entry and compressed-reply widths may themselves come
from another polynomial size estimate in a common problem size. -/
theorem concreteWidth_of_local_bounds {r n E G H N c q : ℕ} (hsize : r+n≤N)
    (hloc : E+G≤polyBound c q N) :
    width r n (BorderBatch.batchLocalWidth n E G) (BorderBatch.batchIncrement n E G) H ≤
      H+polyBound (concreteWidthCoefficient*(c+1)^315) (max q 1 * 315) N :=
  substitute_local_width (coef:=concreteWidthCoefficient) (degree:=315)
    (concreteWidth_bound r n E G H) hsize hloc

/-- A sequence of calls with the same local budgets has linear growth in the
number of invocations, even when the ambient registers start unusually large. -/
theorem concreteWidth_iterate (r n E G H k : ℕ) :
    (width r n (BorderBatch.batchLocalWidth n E G) (BorderBatch.batchIncrement n E G))^[k] H ≤
      H+k*polyBound concreteWidthCoefficient 315 (r+n+E+G) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    apply (concreteWidth_bound r n E G _).trans
    simpa only [Nat.succ_mul, Nat.add_assoc] using
      Nat.add_le_add_right ih (polyBound concreteWidthCoefficient 315 (r+n+E+G))

end LabelRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
