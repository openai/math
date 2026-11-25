import OAI.Hierarchy.DescentDenseHostOrder

namespace OAI
/-! # Transport of a measured right trunk rank to the installed rotor board -/
namespace Hierarchy.DescentDenseHostOrder
noncomputable section
variable {n n' d d' : ℕ} {G : NonlinearExpanders.Graph n d} {G' : NonlinearExpanders.Graph n' d'}
    {r r' H H' : ℕ}

def RightTrunkRank (G : NonlinearExpanders.Graph n d) (r H v : ℕ) : Prop :=
  ∃s : ↥(roster G r H),v=(localRank G r H s).val ∧ ∃key,s.val=.trunk true key

theorem RightTrunkRank.transport (dim : n=n') (deg : d=d') (board : HEq G G') (radix : r=r')
    (height : H=H') {v : ℕ} (tag : RightTrunkRank G' r' H' v) : RightTrunkRank G r H v :=by
  subst n'
  subst d'
  cases eq_of_heq board
  subst r'
  subst H'
  exact tag

end
end Hierarchy.DescentDenseHostOrder

end OAI
