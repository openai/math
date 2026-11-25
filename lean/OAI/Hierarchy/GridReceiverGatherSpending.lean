import OAI.Hierarchy.GridReceiverSpendingSums
import OAI.Hierarchy.TraceReceiverRootFrame

namespace OAI
/-! # Cost of traversing the actual selected root spans -/

namespace Hierarchy.GridChosenReceiver
open TraceFactorReceiver TraceFactorReceiver.Gather
open scoped BigOperators

variable {n : ℕ}

/-- Each actual physical root range contributes exactly the published command test
and 1016 steps per row. The constant remains when the tick got no roots. -/
theorem gather_fuel (base : ℕ) (rows : Fin n → ℕ) :
    Gather.fuel (List.ofFn (rootSpan base rows)) = 6+∑ i, (19+1016*rows i) := by
  simp only [Gather.fuel,List.length_ofFn,List.map_ofFn,Function.comp_def,rootSpan,
    List.sum_ofFn,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,
    ← Finset.mul_sum]; ring

end Hierarchy.GridChosenReceiver

end OAI
