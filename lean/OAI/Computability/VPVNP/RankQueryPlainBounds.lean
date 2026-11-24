import OAI.Computability.VPVNP.RankQueryPlainRoot
import OAI.Computability.VPVNP.RankQueryDescribeBounds

/-!
# Local resource bounds of the ordinary determinant entry routine

Each Cramer entry call contributes its time once and its peak height once.
The additional polynomial work fits the allowance used for the weighted
determinant.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.PlainEngine

open Dispatch

private theorem testClock_le (w : ℕ) : PlainScalar.testClock w ≤ Operation.gram.clock w := by
  have h : (Operation.gram.tree.emitFields capacity (List.finRange 6)).length = 163 := by decide
  rw [PlainScalar.testClock, Operation.clock, h]
  nlinarith [Nat.zero_le ((w+1)^2)]

theorem descriptorClock_le (w v e B x : ℕ) (hw : w ≤ x) (hv : v ≤ x) (he : e ≤ x) :
    descriptorClock w v e B ≤ B + DescribeAdapter.allowance x := by
  have h := DescribeAdapter.overhead_le w v e x hw hv he
  have ht := testClock_le w
  unfold descriptorClock DescribeAdapter.timeWith PlainScalar.clock
  unfold DescribeAdapter.clock DescribeAdapter.timeWith GramScalar.clock at h
  omega

theorem descriptorSpace_le (w v e A S x : ℕ) (hw : w ≤ x) (hv : v ≤ x) (he : e ≤ x) :
    DescribeAdapter.peakWith w v e A (fun a => PlainScalar.space w v e a S) ≤
      max A S + DescribeAdapter.allowance x := by
  have h := DescribeAdapter.overhead_le w v e x hw hv he
  have ht := testClock_le w
  have hmax : max (A+Operation.describe.clock w+PlainScalar.testClock w) S ≤
      max A S + Operation.describe.clock w + PlainScalar.testClock w := max_le (by omega) (by omega)
  unfold DescribeAdapter.peakWith PlainScalar.space
  dsimp only
  unfold DescribeAdapter.clock DescribeAdapter.timeWith GramScalar.clock at h
  omega

end RankQuery.Stack.PlainEngine

end VPVNP
end Computability
end OAI
