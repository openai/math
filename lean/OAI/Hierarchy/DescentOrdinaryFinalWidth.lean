import OAI.Hierarchy.DescentOrdinaryFinalChart

namespace OAI
/-! # Width of the seven physical books returned by an ordinary date -/
namespace Hierarchy.DescentOrdinaryFinal.Chart
open DescentDatedPriorOperand
variable (B : Chart)

def lookupUnit := B.scalarWidth*B.inputs+B.scalarWidth

theorem return_width_le : (B.layout.size+2)*B.layout.nodes≤B.lookupUnit :=by
  have digit : B.field*B.layout.nodes ≤ B.scalarWidth :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  exact digit.trans (Nat.le_add_left _ _)

theorem return_room {h : ℕ} (physical : B.lookupUnit*B.layout.lanes≤h/2) :
    ((B.layout.size+2)*B.layout.nodes)*B.layout.lanes≤h/2 :=
  (Nat.mul_le_mul_right _ B.return_width_le).trans physical

end Hierarchy.DescentOrdinaryFinal.Chart

end OAI
