import OAI.Optimization.LinearProgramming.PriceGame.RecursiveRecovery
import OAI.Optimization.LinearProgramming.PriceGame.ControlExchanges

/-! The exact first-order dispatch specification uses the same campaign, costs, and anchor
as the source proof. The bound here charges designated exchanges. The compiled stack step
clock is proved at the deployment layer. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control

/-- Every legal branch of the actual public solver returns the hidden sign. -/
theorem campaignSolver_recover (i : PublicInput) (positiveRange : 0 < i.range)
    (h : Hidden i.goods i.range i.anchor) (answer : Bool)
    (legal : Computation.Reaches h (campaignSolver Campaign.rounds i) answer) :
    answer = h.positive := by
  have reachable := (Computation.reaches_toTree_iff h (campaignSolver Campaign.rounds i) answer).mpr legal
  rw [campaignSolver, Computation.toTree_ofTree] at reachable
  exact Campaign.recover_sign h positiveRange _ reachable

/-- The charged worst-case number of typed queries, in the exact size parameter of
the bit-machine comparator. -/
theorem campaignSolver_queryBound (i : PublicInput) :
    (campaignSolver Campaign.rounds i).height ≤
      2^1510 * (i.goods + (i.range+1).log2 + 1)^1510 := by
  rw [← Computation.height_toTree, campaignSolver, Computation.toTree_ofTree]
  exact Campaign.recursive_query_bound_machine i.range i.anchor

end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
