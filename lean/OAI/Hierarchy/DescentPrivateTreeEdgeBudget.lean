import OAI.Hierarchy.DescentPrivateTreeGeometry

namespace OAI
/-! Number of edge positions in the actual public fallback-tree catalogue. -/
namespace Hierarchy.DescentPrivateTreeTemplate
open DescentTreePrefixIntervals
open scoped BigOperators
noncomputable section

theorem edge_bound (height : ℕ) : Fintype.card (Edge height)≤2^(height+1):=by
  classical
  have exactSize (t : ℕ) : (∑i : Fin t,2^(i.val+1))+2=2^(t+1):=by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last]
      rw [Nat.pow_succ 2 (t+1)]
      omega
  simp only [Edge,Bits,Fintype.card_sigma,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  have := exactSize height
  omega

end
end Hierarchy.DescentPrivateTreeTemplate

end OAI
